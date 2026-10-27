# Repair: lem-sp-p1-splitting-scalar

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-p1-splitting-scalar.json: existing statement unchanged; proof reassembled in six short steps, 2473 characters total.
- dag/nodes/sec-smooth-purity/lem-sp-finite-tate-balanced-scalar-pullback.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-p1-kummer-derived-scalar.json: statement, unsplit; no Mathlib match.
- citations.json contains an exact statement quotation for each node used by each assembly step. searches.jsonl holds the actual msearch.py results; the two new nodes copy the applicable query records without changing query text.

## Attachments

None. I searched the project declarations by blueprint tag and by coefficient/Kummer/Tate concepts. WeilConjectures has related unit Kummer classes and abstract smooth reduction interfaces, not the full specified projective-line splitting comparison. lean/Sheaf/Paper/P1SplittingScalar.lean has the four helper definitions and p1SplittingScalar; the latter ends in sorry. It is not a finished proof or an attachment. No Lean file was written and no compiler was run.

## Literature wanted

None. The current main-20261015 Charts proof, the unit and chapter records, and the relevant Stacks sources are present.

## What was wrong and what changed

This is the human's 2026-10-21 re-split return, applied on 2026-10-22: the existing six-step proof had 5212 characters and did not expose work that other workers could start separately. The sandbox initially contained only dispatcher markers, no delivered node, report or search log. I therefore copied the current repository item, including its prior proof, searches, citations in prose, Lean metadata and maintainer review. That is also the returned-head proof: its six sizes and content match the return. I kept a full baseline in returned-node.json and preserved the old argument verbatim below. I changed only split-owned fields of the existing item and created two fresh nodes. Delivery rebases split-owned fields onto current main and retains current maintainer/Lean fields.

The two new nodes are independent: neither cites the other or the parent. Both are statement-only (unsplit, empty proof and proof_deps), with the same chapter and unit. They have self-contained objects and canonical comparison formulas, and are of comparable size (1836 and 1930 characters). Neither asserts the splitting equality or trace equality. The item retains the mate calculation, component assembly, coproduct argument and trace cancellation. No statement was shortened or weakened; no route was changed.

## Proof distribution and continuation notes

Old Step 1 and the first half of old Step 4 belong to lem-sp-finite-tate-balanced-scalar-pullback. Their task is the normalization of derived identifications, not just abstract existence of an isomorphism. The complete argument is: the constant line and positive Tate line are locally free of rank one by lem-asd-finite-etale-twist-line. Their degree-zero and shifted complexes are K-flat by lem-pc-kflat-closure. lem-pur-derived-change-of-rings computes extension there by ordinary tensor. The balanced maps and inverses written in the new statement respect the scalar relations and are mutually inverse; for instance ((z tensor a) tensor b) = ((z tensor 1) tensor phi(a)b). The derived functor is exact and additive and hence transports the canonical shifts and finite biproduct maps. For the pullback square, use the roots-induced u_R from lem-asd-etale-finite-twist-pullback and the canonical comparisons of lem-sfb-ringed-derived-monoidal-comparisons. Before shifting, both routes on a pure root tensor send (f^(-1)z tensor a) tensor b to the pulled-back root tensor phi(a)b. Equality after sheafification gives equality of the sheaf maps, their degree-zero derived maps and their shifts. This is the entire old normalization argument, now one separate work item.

Old Step 2 belongs to lem-sp-p1-kummer-derived-scalar, except for its check of the parent's hypotheses, now assembly Step 1. Its task includes identifying the components of the canonical derived composition comparison, which functoriality alone does not name. Use the identity-topos ring tower Lambda -> A -> B and the canonical comparison of lem-sfb-ringed-derived-monoidal-comparisons. Naturality on the single fixed c_Lambda gives alpha_mu[2] E(c_A) = c_B alpha_Lambda. The unit equation identifies alpha_Lambda with multiplication. The K-flat model for composition and flatness of mu_N identify alpha_mu[2] with the specified balanced tensor map, including shifts. The scalar Kummer component in lem-asd-ordinary-finite-p1-adjunction is defined by that very coefficient extension. No Kummer short exact sequence is tensored with a possibly nonflat ring. This is the full old Kummer-transitivity argument, now a separate work item.

Old Step 3 is assembly Step 3, still using the already existing generic mate-transpose node; I did not create a duplicate categorical lemma. The remainder of old Step 4 is assembly Steps 2 and 4, using the two newly exposed upstairs comparisons. Old Steps 5 and 6 remain assembly Steps 5 and 6. The old finite-type/Noetherian/invertible-N check is explicit in assembly Step 1. Thus every argument from the returned proof has a location; the verbatim appendix below makes the accounting checkable.

## Sources and searches

I read the current blueprint proof sk-lem-sp-reduction-exceptional.proof.md, especially Charts, the sk-lem-sp-reduction unit, sec-smooth-purity chapter and the parent det-sp-reduction-exceptional connection. The new nodes cite the exact two sentences of Charts whose geometric normalizations they make precise. The blueprint is agent-written; the parent's proof_origin remains agent. The statement-only children have no claimed proof_origin.

For lem-sp-finite-tate-balanced-scalar-pullback, I read sites-cohomology.tex, Tag 06YQ (sites-cohomology-lemma-bounded-flat-K-flat, line 3120), Tag 06YY (sites-cohomology-lemma-derived-base-change, line 3585), Tag 0D6D (sites-cohomology-lemma-derived-pullback-composition, line 3658) and Tag 07A4 (sites-cohomology-lemma-pullback-tensor-product, line 3684), together with the actual statements of the finite twist and roots-induced pullback nodes. For lem-sp-p1-kummer-derived-scalar, I read the same Tag 0D6D proof on a common K-flat representative and the monoidal comparison node's unit formula, plus the ordinary finite p1-adjunction statement's definition of the scalar-extended Chern class. These Stacks tags support the generic ingredients; the new specialized geometric comparison statements are sourced to the blueprint Charts argument, not misattributed verbatim to a generic Stacks theorem. No SGA source is used.

Before creating the nodes I searched the entire DAG by statement concepts, the full imported blueprint using blueprint_refs.py search Kummer, scalar, twist, balanced and Kummer.*scalar, and the Lean source by the same notions and the precise ids. blueprint_refs.py ancestor returned det-sp-reduction-exceptional; both new from.via lists contain the present item. No blueprint node states either specialized ordinary-etale comparison, so same_as is empty. Important near matches are distinguished below.

All new-node Mathlib searches actually ran through msearch.py with two semantic phrasings per proposed statement, Loogle and a whole-Mathlib grep. I also ran fresh item searches because there was no local prior search log, while retaining every historical mathlib_searches entry in the baseline. The returned records and actual hits were read. No service was unavailable. Search hits concern etale ring algebras, Kaehler differentials, Picard groups of rings, roots of unity in a single ring, or ordinary free/presheaf tensor constructions. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean lines 118-143: pullbackObjFreeIso is about a globally free sheaf and its generator maps, not the derived roots-induced Tate normalization and its coefficient/pullback square. It is not a one-line specialization to the stated lemma. KummerDedekind concerns ideal factorizations, not a Kummer Chern morphism. CommRing.Pic.mapAlgebra_mapAlgebra concerns a Picard group of rings, not the normalized derived etale class. Hence no new node is a Mathlib leaf.

## Not duplicates

lem-sp-finite-tate-balanced-scalar-pullback vs lem-asd-finite-etale-twist-line: the existing node supplies local freeness and flatness at one coefficient ring; the new node constructs the specified derived coefficient isomorphisms and their roots-induced pullback square across A -> B.
lem-sp-finite-tate-balanced-scalar-pullback vs lem-asd-etale-finite-twist-pullback: the existing node handles scheme pullback at a fixed ring and exponent; the new node proves agreement with balanced derived coefficient extension across two rings.
lem-sp-finite-tate-balanced-scalar-pullback vs lem-pur-coefficient-pullback-coherence: the existing node is a coherence assertion for already supplied Comparisons and units; the new node constructs the degree-zero and derived finite Tate comparisons and identifies the concrete root square.
lem-sp-finite-tate-balanced-scalar-pullback vs lem-pur-signed-line-scalar-normalization-data: the existing node defines a predicate on supplied signed-line comparisons, and asserts no existence or derived identification.
lem-sp-finite-tate-balanced-scalar-pullback vs lem-sp-invertible-tensor-scalar-extension: the existing node concerns ordinary tensor powers and duals of an abstract line, with no roots-induced scheme-pullback square or derived degree-zero agreement.
lem-sp-finite-tate-balanced-scalar-pullback vs lem-weil-integral-twist-derived-scalar: the existing node concerns completed integral pro-etale coefficients and field extensions, not arbitrary finite ordinary-etale coefficient maps.
lem-sp-p1-kummer-derived-scalar vs lem-sp-finite-p1-kummer-naturality: the existing node handles geometric base change S' -> S at one fixed coefficient ring; the new node handles derived extension A -> B on the same projective line and identifies the coefficient-composition components.
lem-sp-p1-kummer-derived-scalar vs lem-asd-supported-kummer-boundary-scalar: the existing node is the supported relative boundary of an effective Cartier immersion and the map Z/N -> A; the new node concerns the global projective Chern morphism and arbitrary A -> B with normalized transitivity.
lem-sp-p1-kummer-derived-scalar vs lem-amb-cartier-kummer-naturality: the existing node gives naturality of already realized ordinary/pro-etale Cartier families and positive quotient reductions, not arbitrary finite-ring derived coefficient transitivity for the projective Chern arrow.
lem-sp-p1-kummer-derived-scalar vs lem-pur-kummer-coefficient-base-change: the existing node assumes a coefficient module free over Z/ell^N and treats Kummer cohomology; the new node allows arbitrary finite A -> B and compares actual derived morphisms.
lem-sp-p1-kummer-derived-scalar vs def-asd-ordinary-finite-p1-kummer-class: the existing node defines an abelian cohomology realization; the new node is a theorem identifying actual module-derived coefficient-composition maps and their boundary normalizations.
lem-sp-p1-kummer-derived-scalar vs lem-asd-ordinary-finite-p1-adjunction: the existing node defines and proves the splitting at each fixed coefficient ring and its geometric base change, but does not assert this arbitrary A -> B scalar compatibility.
lem-sp-p1-kummer-derived-scalar vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node supplies general monoidal composition; the new node identifies its components on the concrete etale Kummer source and Tate target. The generic lemma remains the tool for the extracted normalization argument.
lem-sp-finite-tate-balanced-scalar-pullback vs lem-sp-p1-splitting-scalar: the new node has no direct-image splitting or trace, only the coefficient identifications and twist pullback square.
lem-sp-p1-kummer-derived-scalar vs lem-sp-p1-splitting-scalar: the new node has no beta, splitting or trace, only the upstairs Chern morphism and the coefficient-composition normalization.

## Review by Q08

I checked this repair against delivery-errors B-E with the node statements and source paragraphs open. The new statements introduce N, the schemes, finite rings, the ring map, the derived categories, the twist sheaves and the canonical maps. The inherited notions are cited explicitly; the elementary definition of roots and the Noetherian condition are also written out. New nodes carry no proof sketch in their statement, no proof steps and no proof dependencies. Their substantive assertions are the derived-normalization and morphism equalities, not the parent conclusion under a new name.

Assembly Step 1 uses the finite-type-over-Noetherian node exactly for Noetherianity of S. A field is Noetherian, finite type is in the standing hypotheses, and N is a power of a prime different from char(k), including n=0. Its other citation, lem-sp-finite-tate-balanced-scalar-pullback, explicitly provides all balanced isomorphisms, the pullback square, the shift and finite-sum comparisons used there. Step 2 uses lem-sp-p1-kummer-derived-scalar's displayed derived Chern equality, and the ordinary p1-adjunction node explicitly states that the two components are the shifted twisted unit and h. Its Noetherian and invertible-N hypotheses have already been checked. Step 3 uses only the coefficient-compatibility node's proper counit-transpose normalization and the mate-transpose node's actual equality under the two adjunctions. I checked its orientation by the written transpose and triangle calculation. Step 4 specializes that identity to the two source objects; the new pullback-square lemma supplies u_B and the Chern lemma supplies c_B. Step 5 is coproduct extensionality, with inclusions preserved by the stated additive comparison. Step 6 uses exactly the trace definition t = pr_2 s^(-1), then functoriality and cancellation of T(s_A). These last arguments are elementary from the earlier steps, not uncited comparison theorems. citations.json quotations are all verbatim substrings, checked individually.

For the new balanced-line statement I verified the direction and domains of theta and lambda: the left composite starts at f_B^* E_T(A_T(1)) and ends at B_T'(1), just as the right composite does. The unit version has the same direction. Before shifting both routes send a root tensor to the pulled-back root tensor phi(a)b; no assumption that tensor commutes with arbitrary section groups is used, only the sheafified local pure-tensor presentation. For the new Chern statement, the source of theta^1[2] E(c_A) and c_B theta^0 is E(A_P); both targets are B_P(1)[2]. The coefficient tower's source component is the multiplication unitor, not an arbitrary automorphism of B_P, and its target is the stated balanced map. This is why these are two actual arguments suitable for separate workers, not a purely formal renaming of the final equality.

I tested identity coefficient maps (both balanced maps become their unitors), the empty base, zero rings, N=1, and the nonflat Z/ell^2 -> F_ell. When N=1 every killed coefficient ring is zero, so all asserted maps are the unique maps of zero objects. Empty bases behave the same way. For the nonflat quotient the twist lines remain flat over their own coefficient rings; the K-flat calculation and derived composition remain valid without tensoring a Kummer short exact sequence. This addresses E1/E2 and the central nonflatness risk. The two nodes are not clauses of the parent's splitting/trace conclusion and do not depend on it, so the repair spreads work without a cycle. The parent has no step longer than 2000 characters; its total is below 3000. I found no mathematical statement dispute and made no change to its statement. Existing maintainer metadata and import fields were retained; accepted old tool-use metadata was not rewritten.

The only correction needed here was structural: isolate both nontrivial normalization arguments and expose their complete conclusions. I retained the original Noetherian hypothesis check, normalized actual arrows, nonflatness justification, transpose orientation, coproduct proof and trace cancellation. The full old proof follows for audit and for the workers who take the new nodes.

## Unfinished work

The two new nodes intentionally await stage-1 splitting by other workers. There is no missing argument in the parent's assembly relative to their stated conclusions. No Lean proof is claimed.

## Verbatim returned proof (preserved, with new destinations above)

### Old Step 1

Normalize the scalar identifications before comparing arrows. For T=S,P, the sheaves A_T and A_T(1) are flat, and A_T(1) is locally free of rank one by [lem-asd-finite-etale-twist-line]. Their degree-zero complexes and shifts are K-flat by [lem-pc-kflat-closure]. Thus [lem-pur-derived-change-of-rings] computes their scalar extension by ordinary tensor. The balanced map (z\otimes a)\otimes b\mapsto z\otimes\varphi(a)b has inverse z\otimes b\mapsto(z\otimes1)\otimes b; these formulas are balanced and mutually inverse. They give exactly the twist identifications in the statement. The scalar functor is exact and additive by the same derived-change-of-rings assertion, hence preserves shifts and finite biproducts with their inclusions and projections. Write D_R=R_S(1)[2]\oplus R_S and identify T_S D_A=D_B by these maps.

Uses: lem-asd-finite-etale-twist-line, lem-pc-kflat-closure, lem-pur-derived-change-of-rings.

### Old Step 2

Put \Lambda=\mathbf Z/N and let c_\Lambda:\Lambda_P\to\mu_{N,P}[2] be the Kummer Chern morphism of the fixed line bundle \mathcal O_P(1). Write E_{\Lambda R} for derived scalar extension on P. The definition of the scalar-extended Kummer class in [lem-asd-ordinary-finite-p1-adjunction] says that the upstairs morphism whose q-adjunct is h_R is c_R=E_{\Lambda R}(c_\Lambda). Apply [lem-sfb-ringed-derived-monoidal-comparisons] to the identity-topos ring tower \Lambda_P\to A_P\to B_P. Its canonical composition isomorphism \alpha:T_P E_{\Lambda A}\simeq E_{\Lambda B} is natural on c_\Lambda, so \alpha_{\mu_N[2]}T_P(c_A)=c_B\alpha_{\Lambda_P}. The source component is the multiplication unit, and the target component is the balanced map of Step 1: the cited comparison is computed by ordinary module pullback composition on K-flat complexes. Therefore T_P(c_A)=c_B under the specified identifications. This is naturality of the image of one fixed Kummer morphism; it does not tensor the Kummer short exact sequence with a nonflat coefficient ring. The hypotheses of [lem-asd-ordinary-finite-p1-adjunction] hold for R=A,B: S is of finite type over the Noetherian scheme \operatorname{Spec}k, hence Noetherian by [lem-weil-pbc-finite-type-over-noetherian] (quasi-compact and locally Noetherian, so it has a finite affine cover by spectra of Noetherian rings); N=\ell^n is invertible on S because \ell\ne p=\operatorname{char}k; and A,B are finite commutative rings with NA=NB=0.

Uses: lem-asd-ordinary-finite-p1-adjunction, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-finite-type-over-noetherian.

### Old Step 3

Let \lambda_X:q_B^*T_SX\xrightarrow{\sim}T_Pq_A^*X be the canonical tensor/pullback comparison. It is the left square whose right mate is the specified \beta_q: this is precisely the proper counit-transpose normalization in [lem-sp-et-proet-coefficient-compatibility]. For any v:q_A^*X\to E let \operatorname{adj}_R denote the inverse-image/direct-image adjunction bijection over R. Apply [lem-pur-adjunction-mate-transpose] to this square. It gives the equality of actual morphisms
$$\beta_q(E)T_S(\operatorname{adj}_A(v))=\operatorname{adj}_B(T_P(v)\lambda_X).$$
The orientation can also be checked directly: the B-transpose of the left side is T_P(\varepsilon_{A,E})\lambda_{Rq_{*,A}E}q_B^*T_S(\operatorname{adj}_A(v)); naturality of \lambda and the A-triangle identity turn this into T_P(v)\lambda_X. Thus the equality uses the named counit-transpose map rather than an arbitrarily chosen isomorphism between the endpoints.

Uses: lem-sp-et-proet-coefficient-compatibility, lem-pur-adjunction-mate-transpose.

### Old Step 4

Write u_R:q_R^*(R_S(1)[2])\xrightarrow{\sim}L_R for pullback of the roots-of-unity twist. By [lem-asd-etale-finite-twist-pullback] it is the canonical roots-induced identification. It satisfies T_P(u_A)\lambda_{A_S(1)[2]}=u_B under Step 1: both composites before shifting send (q^{-1}z\otimes a)\otimes b to the pulled-back root z\otimes\varphi(a)b. Equality of these sheaf maps gives equality of their degree-zero and shifted derived maps. The tensor and unit comparisons used here are the canonical ones of [lem-sfb-ringed-derived-monoidal-comparisons]. The two components of s_R are \operatorname{adj}_R(u_R) and \operatorname{adj}_R(c_R), by [lem-asd-ordinary-finite-p1-adjunction]. Apply Step 3 first to v=u_A and then to v=c_A; Step 2 identifies the scalar extension in the second application. Consequently
$$\beta_q(L_A)T_S(\operatorname{adj}_A(u_A))=\operatorname{adj}_B(u_B),\qquad \beta_q(L_A)T_S(h_A)=h_B.$$
Here q_B^*T_S A_S=B_P, so the latter equality has the asserted unit source, not a restriction-of-scalars source.

Uses: lem-asd-etale-finite-twist-pullback, lem-sfb-ringed-derived-monoidal-comparisons, lem-asd-ordinary-finite-p1-adjunction.

### Old Step 5

Let \iota_{1,R},\iota_{2,R} be the two inclusions of D_R. Step 1 identifies T_S(\iota_{j,A}) with \iota_{j,B}. For j=1,2 Step 4 therefore gives
$$\beta_q(L_A)T_S(s_A)\iota_{j,B}=s_B\iota_{j,B}.$$
The universal property of the coproduct D_B says that maps out of it agreeing on both inclusions agree. Hence \beta_q(L_A)T_S(s_A)=s_B, the first required equation.

Uses: elementary.

### Old Step 6

Use the specified definition t_R=\operatorname{pr}_{2,R}s_R^{-1} of [def-amb-p1-trace]. Postcomposing the first equation with t_B gives t_B\beta_q(L_A)T_S(s_A)=\operatorname{pr}_{2,B}. Functoriality and Step 1 also give T_S(t_A)T_S(s_A)=T_S(\operatorname{pr}_{2,A})=\operatorname{pr}_{2,B}. Since s_A is invertible, T_S(s_A) is invertible with inverse T_S(s_A^{-1}); cancel it on the right. This proves t_B\beta_q(L_A)=T_S(t_A). All tensor computations were made on K-flat objects, and the other steps used functoriality, adjunction and coproduct identities. No flatness of B over A is used.

Uses: def-amb-p1-trace.

