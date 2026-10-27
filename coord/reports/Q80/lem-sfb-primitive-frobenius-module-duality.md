# Worker report: lem-sfb-primitive-frobenius-module-duality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-primitive-frobenius-module-duality.json: split the unchanged statement in eight explicit steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-restricted-symmetric-basis.json: new statement-only lemma, status unsplit; no Mathlib match. Arbitrary-dimensional abelian restricted PBW basis, not just finite-dimensional restricted Lie algebras.
- dag/nodes/sec-six-functors-basics/lem-sfb-connected-filtered-coalgebra-kernel-primitive.json: new statement-only lemma, status unsplit; no Mathlib match. Detection of a nonzero kernel by a primitive element for a connected filtered coalgebra.
- citations.json: a verbatim statement quotation for each of the 21 cited-node occurrences. The quotations are whole statements, so that all the exact hypotheses remain visible.
- report.md, this report. searches.jsonl was produced by the authorized msearch.py command, not synthesized.

## Attachments

None. Searched the live project WeilConjectures/ for the exact blueprint tag, primitive functions/elements, restricted PBW, and skew-polynomial notions. Its semilinear Frobenius module file discusses Lang--Steinberg; it does not state the group-scheme reconstruction. The ordinary primitive field element declarations do not apply. No compiler, Lake, or Lean writing was used.

## WANTED

None. Milne, Algebraic Groups (2017), is present as literature/milne-algebraic-groups_iAG2017.pdf and was read directly with pdftotext.

## What needed repair in the imported material

The item was an unsplit statement with no proof, and the sandbox contained no prior node or report. Its statement agrees with Milne Theorem 14.46 interpreted through Proposition 14.41 and the explicit universal functor, and was retained verbatim.

Two potentially circular shortcuts were avoided explicitly. A module finite over k_sigma[F] need not be finite-dimensional over k (the module A itself is the basic example), so the existing finite-dimensional restricted PBW node cannot be applied. Also finite generation of P(G) is part of the conclusion, so B(V,F) is first constructed for an arbitrary vector space V with semilinear F. Only after the injection argument is proved do the finitely many embedding coordinates give P(G) as their A-span.

The proof follows the restricted enveloping construction and primitive calculation in Milne 14.41--14.43. It supplies an algebraic kernel argument in place of the quotient/multiplicative-type argument of 14.44. Thus proof_origin is agent, even though the construction and coefficient calculation are read from Milne. This is a choice below the unit route, not a replacement for a step of a chapter or unit. No SGA source is cited.

I read the current latest blueprint proof at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, in particular its (3), as well as the chapter and imported unit records. The imported item's long ancestry reaches the former alteration subbranch of that direct-image proof. The current latest text gives the proper/open/compactification route. I did not edit that route or any ancestry record. tools/blueprint_refs.py ancestor prints node None for this already-created ancestry; the new records preserve that computed value and prepend this item to via, rather than inventing a blueprint ancestor.

## Not duplicates

lem-sfb-semilinear-restricted-symmetric-basis vs lem-sfb-restricted-pbw-basis: the existing statement assumes a finite-dimensional Lie algebra. The new statement allows any vector-space dimension, with zero bracket and an arbitrary additive Frobenius-semilinear operator; infinite dimension is necessary even for M=A. The general finite-dimensional nonabelian statement does not specialize to this one.

lem-sfb-semilinear-restricted-symmetric-basis vs lem-sfb-unipotent-restricted-enveloping-augmentation: the existing statement is about the finite-dimensional Lie algebra of the unipotent radical of a semisimple simply connected group over an algebraically closed field, and gives dimension and nilpotent augmentation; it does not give this arbitrary semilinear quotient basis.

lem-sfb-semilinear-restricted-symmetric-basis vs lem-sfb-enveloping-universal-property: the existing statement concerns ordinary enveloping algebras over Q, not restricted enveloping algebras in characteristic p or a truncated basis.

lem-sfb-connected-filtered-coalgebra-kernel-primitive vs lem-sfb-filtered-coalgebra-nonzero-coinvariant: the existing statement supplies a nonzero coinvariant in a comodule, not a primitive element in the kernel of a coalgebra map. A coalgebra-map kernel is a coideal, and is not assumed a subcomodule. Applying that existing node to the kernel would be invalid.

lem-sfb-connected-filtered-coalgebra-kernel-primitive vs lem-sfb-hopf-subalgebra-faithfully-flat: the existing statement starts with an injective map of finitely generated Hopf algebras and deduces flatness; the new lemma detects injectivity without an algebra structure or finite generation. It supplies neither faithful flatness nor a quotient group.

Before creation I searched the whole DAG for restricted symmetric, truncated monomial, PBW/10.40, primitive elements, Hopf ideals, and connected filtered coalgebra statements, and ran blueprint_refs.py searches for primitive function, restricted symmetric, semilinear restricted, truncated monomial, PBW, Hopf ideal, connected filtered coalgebra, and symmetric algebra. The two Hopf blueprint matches concern the characteristic-zero geometry conventions; the Frobenius-module blueprint matches concern linear Weil modules. Neither states either new lemma. The existing affine Hopf construction, Hopf spectrum functor, symmetric universal property, tensor algebra structure and vector-space basis statements are reused, rather than duplicated.

## Review by Q80

I read Milne 14.40--14.46 (printed pp.292--295), including the arbitrary basis index set I and coproduct formula in 14.43, and Definition 10.39/Theorem 10.40 (printed pp.206--207). These justify the new basis statement for an abelian restricted Lie algebra of arbitrary dimension: zero bracket makes the Jacobson cross terms vanish and the restricted operation is exactly the additive semilinear T. The new statement does not assume k is perfect. I also read Definition 14.4 and the filtered-coalgebra argument referenced from Theorem 14.5 (printed pp.281--282) for the second node. Its precise kernel assertion is my general algebraic lemma, not a claim that Milne 14.44 states it.

Here is a proof guide for that second node, kept outside its statement. Choose the least n with a nonzero x in ker(f) intersect C_n. The counit equation gives epsilon(x)=0, while f is injective on C_{n-1}; n cannot be zero since f(g) has counit 1. Put pi(y)=y-epsilon(y)g. The reduced coproduct of x is (pi tensor pi)Delta(x), and the filtration puts it in C_{n-1} tensor C_{n-1}: the extreme terms involving C_0 disappear. Its image under f tensor f is zero. An injection of vector spaces has a linear left inverse on its image, extended to the target by choosing a basis complement; tensoring this left inverse with itself proves injectivity on that tensor subspace. Hence the reduced coproduct vanishes and x is the required nonzero primitive. This argument also covers n=1 and arbitrary dimension.

For the first node, the future split can use Milne's arbitrary-index restricted PBW theorem directly. Equivalently, after choosing a basis, the relations X_i^p minus the linear expression for T(e_i) have mutually relatively prime leading monomials X_i^p in the total-degree order; the overlapping reductions commute, giving precisely the truncated monomials. This is a genuine basis theorem, not an elementary new-node wrapper for a clause of the item.

For step 1 I opened def-weil-affine-spectrum (the exact contravariant morphism correspondence), def-sc-gm-ga (the additive coordinate comultiplication), lem-sfb-affine-group-coordinate-hopf (all counit and antipode identities), and def-weil-ring-frobenius (additivity, multiplicativity and iteration). They provide exactly the structures used to identify group homomorphisms with primitives and define the skew action. The coordinate map of Frobenius fixes k and sends t to t^p; there is no assertion that absolute Frobenius is k-linear over an imperfect field.

For step 2 I read the new basis node, the full symmetric-algebra universal property and the algebra-quotient definition. An algebra map factors through the displayed ideal precisely when it kills each v^p-Tv. Respecting k and F is equivalent to respecting the skew-polynomial action, not to ordinary k[F]-linearity. This constructs B for every V; it uses no claimed finiteness of P(G).

For step 3 I read the tensor-pushout universal property, Frobenius node and Hopf-spectrum functor. The latter really constructs a group scheme from the Hopf maps and takes Hopf morphisms to group morphisms. The proof checks every Hopf identity on j(V) using the uniqueness proved in step 2; it does not misuse the coordinate-Hopf theorem in the reverse direction. The sign formula is valid also in characteristic two.

For step 4 I opened the finite-module definition, finite-type algebra definition, closed-immersion affine-quotient criterion, finite-type morphism definition and additive-group definition. Finite A-generators give algebra generators because j(F^im)=j(m)^(p^i), so a finite affine presentation proves finite type and the desired group embedding. Finite presentation of M over A, Noetherianity of A and perfection of k are not needed. Quotients of a finite-variable polynomial ring already give the required finite type.

For step 5 I checked the new basis statement and lem-weil-pbc-vector-space-free. The primitive calculation is written out in coefficients: for a fixed multi-index a and a_i>0, the tensor b_delta_i tensor b_(a-delta_i) can come only from a, and its coefficient is a_i. The inequalities 0<a_i<p are what make this coefficient invertible in k. Tensor coordinate functionals justify independence of these pure tensors, including for infinite basis sets since every expression has finite support. No claim about characteristic-zero primitives or an arbitrary Hopf algebra is substituted. This also explicitly verifies all hypotheses of the filtration lemma needed by step 6.

For step 6 I opened the complete new filtered-coalgebra-kernel statement. Its hypotheses match: C there is B(V,T), distinguished g is 1, D is the ambient coordinate Hopf algebra, q preserves comultiplication and counit, and step 5 gives its exhaustive connected filtration. The lemma supplies a kernel primitive; step 5 and the inclusion V in the target then contradict it. The absence of finite generation in the lemma matters at this exact step.

For step 7 I reread the closed-immersion affine-quotient criterion and additive coordinates. The images x_s really generate the whole coordinate ring as an algebra, because the defining morphism is a closed immersion, not just a map with dense image. Their A-span N is a subspace of P(G). Steps 5 and 6 apply to N with no extra hypothesis and show B(N) is exactly the coordinate ring. Identifying primitives then gives P(G)=N. This proves rather than assumes the finiteness required in the item's conclusion.

For step 8 the affine-spectrum statement gives an actual isomorphism of schemes from the algebra isomorphism. The explicit point formula is the composite C to R evaluated on the primitive coordinate f; this proves both the specified evaluation map and its compatibility with all coefficient algebras. The point formula is not tested only over fields.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 of delivery-errors against the open files: the two new nodes are self-contained statements with empty proof/dependency lists, use existing definition nodes, record the actual search queries, and do not restate clauses of the item. The kernel lemma is a generic characteristic-independent coalgebra result; the basis lemma does not mention group schemes or evaluation. All item steps are under 1000 characters, so no over-2000-character step hides a comparison lemma. No statement correction or dispute was needed. No off-route non-Mathlib lemma is cited: the two new lemmas share the item's unit and the other results are Mathlib leaves or definitions.

Small cases checked: V=0 gives B=k, no nonzero primitives and the trivial group; M=A gives the polynomial algebra k[t], with the infinite k-basis 1,F,F^2,... of M and Frobenius chain mapping to t,t^p,t^(p^2),...; M=A/AF gives k[t]/t^p and alpha_p, so nonreduced groups are retained. A one-dimensional semilinear module with T(e)=e gives k[t]/(t^p-t), with primitives spanned by t, so finite etale groups are retained. Over an imperfect field, T(e)=a e has the same monomial basis and needs no pth root of a. For the kernel lemma the counit map k[t] to k has kernel containing primitive t; in characteristic p the quotient by t^p has primitive kernel element t^p, so one cannot replace its conclusion by a fixed chosen degree-one subspace. This is why step 5, rather than a spurious degree assumption, is used in step 6.

The initial server review_split returned PASS. The full deliver.py dry run and final push are run after this report and citation audit.

## Unfinished

No unfinished portion of the assigned one-level split. The two new statement-only nodes intentionally remain for later stage-1 splitting; no Lean proof completion is claimed.
