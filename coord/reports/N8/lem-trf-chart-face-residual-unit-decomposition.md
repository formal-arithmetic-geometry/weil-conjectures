# Stage-1 report: lem-trf-chart-face-residual-unit-decomposition

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-chart-face-residual-unit-decomposition.json`: statement, split into eleven checked steps; no Mathlib match for the entire item.
- `citations.json`: eighteen verbatim statement quotes, one for each citation of each step.
- `report.md`: this report.

No new nodes, no new Mathlib leaves, no unit edits, no Lean edits or compiler invocations. The sandbox initially contained only dispatcher markers; there was no prior split or report to resume. The inherited node and all inherited search records were retained. New searches are appended from this session's `searches.jsonl` with their exact tools and query strings.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for residual units, face localization, monoid sharpening and saturated monoids. The only initial chart/face phrase hit was unrelated cube formalism. No project declaration states this item, including its explicit twisted tensor maps. Mathlib hits about coefficient tensor equivalences, Grothendieck group lifts, localization, units and characters do not give the whole assertion. Two different semantic phrasings, Loogle, LeanSearch and source grep were run with the required msearch command; all services answered. No search was invented or treated as unavailable when it answered.

## WANTED

None. Read the available ILO PDF, VI 1.1--1.6 (printed pp. 69--70, PDF pp. 75--76) and VIII 3.1.1--3.1.5 (printed pp. 98--99, PDF pp. 104--105). These give localization, sharpening, local monoid homomorphisms and the chart setting, not the full tensor formula. Accordingly the proof is explicitly agent-written. Read Stacks `algebra.tex` at labels `lemma-tensor-product` (00CX, in section 00CV), `definition-localization` (00CO), the prime-local-ring paragraph (07BH), `lemma-characterize-local-ring` (00E9), and `section-completion` (00M9). The algebra tensor universal property is cited via its existing Mathlib-leaf node. Read the additive monoid algebra lift and its uniqueness formulas in Mathlib `Algebra/MonoidAlgebra/Basic.lean`, lines 607--651, as specified by the existing leaf.

## STATEMENT-DISPUTED: missing homomorphism hypotheses and an untyped extension

The imported text merely says "suppose a:S→(A,·) and epsilon:R^gp→A^× satisfy ..."; unlike its explicit requirement on alpha, it never says these two maps are homomorphisms. The subsequent ring map Z[S]→A and the use of chi as a character require this. The factorization alone does not imply it.

Counterexample to the literal raw formulation: take A=Q[[t]], R=Q=N, h=id, alpha(n)=t^n, G=0 and S=N. Let u(2)=2 and u(n)=1 for all other nonnegative integers. Put a(n)=u(n)t^n and epsilon(n)=u(n)^(-1) for n≥0; define epsilon(n)=1 for negative n. All epsilon values are units and alpha(n)=epsilon(n)a(n), with a(0)=epsilon(0)=1. Nevertheless a(2)=2t² differs from a(1)²=t², so there is no ring homomorphism Z[S]→A sending [s] to a(s), and epsilon is not a group character. The claimed tensor algebra is thus not even defined under that literal reading. Take the prime (t) of C=A to meet the other hypotheses.

Correction: state explicitly that a is a monoid homomorphism and epsilon is a group homomorphism, as the title, use of character, parent node and intended monoid-chart setting require. Also define alpha_G(r−g)=alpha(r)alpha(g)^(-1) and use alpha_G(x) in the factorization on R_G; previously alpha had domain R but was applied on R_G without an extension being introduced. Step 1 verifies that extension is well defined. No claimed conclusion was removed or weakened. Apart from these explicit intended typing hypotheses, the statement is unchanged.

## What was wrong or incomplete

The node was statement-only; its source correctly calls it an agent refinement rather than a verbatim ILO theorem. I did not treat the formal-chart description as a proof of the tensor isomorphism. The proof now exhibits both maps, their balancing identities, the independence under N, the inverse calculations, and the prime and completion maps.

The latest blueprint (`literature/blueprint/latest/`, current 2026-10-23 snapshot) now proves the top-level local-term locality using contracting correspondences rather than the historical nearby-duality/alteration branch recorded in this node's ancestry. I read its current local-term proof and unit text. This delivery proves the explicitly assigned historical algebraic subnode independently; it neither changes a unit nor restores the old top-level route. The inherited source and ancestry are retained. There is no released repair note for this item.

## Not duplicates

There are no new nodes. Whole-DAG searches by face localization, sharpening, residual units and group sections led to reuse, rather than copies, of existing nodes. Whole-blueprint searches with `blueprint_refs.py search` for `sharpening`, `face localization`, `monoid algebra`, `residual unit` and `character twist` found no blueprint statement of this whole item (the sole sharpening hit was an unrelated Fourier node). The item's `same_as` remains empty.

The face-sharpening node gives units, sharpness, saturation and free sharp group completions, but no residual quotient by N or twisted tensor. The group-section/product node applies after identifying P, K and its group exact sequence, but contains no local-ring or monoid-algebra claim. The subgroup node is precisely the already available finite-free subgroup input. The ideal-tensor nodes `lem-trf-monoid-face-localization-ideal-tensor` and `lem-trf-monoid-unit-twist-ideal-tensor` concern ideal tensors with a fixed evaluation to A and do not themselves assert this A-algebra isomorphism; this delivery proves the ring-map assembly using the existing universal properties. Nothing was made into a new node that merely restates a clause of the item.

## Review by N8

I read the source passages above and every cited node's statement, not just its proof or title. There is no new node needing its own source review. I checked delivery-errors B--E against the actual item and citations, with the following substantive checks.

Step 1 uses the prime-localization definition for B's maximal ideal, and the local-ring unit criterion exactly in the direction that a member of m maps into qB and cannot be a unit. The contraction hypothesis is essential here and is present. The tensor relation is the balancing relation of the cited tensor-product definition. The face property and the well-defined alpha_G formula are written out. This reasoning never assumes A→B injective or flat.

Step 2 applies `lem-trf-fs-face-sharpening` twice. I verified that its statement supplies every claimed clause: localized units, sharp fs quotients, embeddings into the quotient groups, and finite free group completions. Its fs and face hypotheses were respectively assumed and proved in Step 1. The quotient isomorphism M≅S^gp follows from the given h^gp isomorphism, not an assumed sharp-map injection.

Step 3 proves the residual quotient embeds in M, proves its group completion is M, identifies the kernel K, and proves the inverse-image characterization by adding an actual F^gp unit. These are short quotient/group calculations using Step 2, not hidden structure theorems. In particular P^×=K follows from sharp T and availability of both signs of K.

Step 4 uses the exact finite-free-subgroup conclusion of `lem-weil-subgroup-finite-free-abelian-group-free` after choosing the finite basis of M already provided by Step 2. It then applies `lem-trf-group-section-monoid-product` with P and T, not with Q_F whose unit group can have torsion. I verified integrality, the precise group completions, surjectivity, kernel equal to all units, and a finite basis of T^gp. The node provides a group section whose restriction lands in the monoid, and both inverse maps; interchanging its two product factors gives exactly the requested order K⊕T.

Step 5 proves the nonzero-coordinate clause from the explicit identity Q∩F^gp=F, using the face equation q+f₂=f₁. Pullback of F along h is exactly G by Step 1. It proves the q-coordinate criterion at the same time. No injectivity of S^gp→T^gp is inferred.

Steps 6, 7 and 9 cite the integer monoid-algebra universal property for extension of a multiplicative function on monomials, and the algebra-tensor pushout universal property for the compatible pair of ring maps. I checked that these nodes say existence and uniqueness of the full ring homomorphisms, not merely an additive or module statement. The balancing checks are explicit: chi(h(r))[f(r-bar)]=alpha(r) in the forward direction and y(f(s))=epsilon(x)^(-1)alpha_G(x)=a(s) in the reverse direction. The scalar character is a genuine homomorphism under the corrected explicit hypothesis. F-monomials map to units because their classes belong to K, so extension to C_F is legitimate; the fraction formula supplies independence and the formula asked for in the conclusion.

Step 8 is the critical residual-unit descent: for t∈G^gp, alpha_G(t)=epsilon(t) because its S-class is zero. Thus replacing w by w+h(t) changes chi(w)^(-1)z(w) by the factor epsilon(t)^(-1)alpha_G(t)=1. I checked signs and both uses of h^gp. It never cancels a nonunit of A and works when A→B kills nonzero elements. Independence of the Q_F representative is an equality of monomial products before localization.

Step 10 checks both composites on monomials and coefficients; tensor generation is explicitly in the cited tensor-product node. Fractions are then fixed because an algebra map preserves inverses. Reindexing the free monomial basis by the proved monoid isomorphism is multiplicative and preserves f's balancing relations, so it gives the displayed algebra tensor with K⊕T, not just an additive equivalence.

Step 11 checks all F-denominators avoid q, writes the two fraction maps comparing the chosen localizations, and applies the algebra isomorphism to the corresponding prime. It then maps every maximal-ideal power and every compatible quotient sequence, using precisely the completion definition. This proves the completion comparison without Noetherianity, excellence or a flat-completion theorem. The citation to the local-ring criterion says exactly the nonunit fact used here.

I checked that every citation has a full verbatim statement in `citations.json`, and that proof_deps is exactly the union of uses. The dependency closures of all supporting nontrivial nodes avoid this item. All non-elementary steps are under 2000 characters; none conceals a separate unproved comparison. Every off-unit citation is already a Mathlib leaf, so no additional route tool declaration is needed. No SGA source is used.

Small cases checked: R=Q=0, h=id and the identity character; R,Q equal to a finite abelian group (all elements units, so the sharp groups and K vanish, despite torsion in the original group completion); G=R (then S=0, and the group-isomorphism condition forces F=Q and T=K=0); an ordinary N-chart with alpha(1)=t and a multiplicative scalar unit twist; and a case where residual K is nonzero and the sharp group map is not injective. For the last take R=N², Q=N·u⊕N·z with h(e₁)=u+z and h(e₂)=z, A=Q[[t]], alpha(e₁)=alpha(e₂)=t and epsilon=1. Then C=A[U]/(t(U−1)); at q=(t,U−2) we have G=0, F=N·u, K=Z·u, T=N·z, and f(a,b)=(a,a+b). Thus beta^gp has kernel Z(1,−1), while beta(s) is nonzero for every nonzero s∈N². The resulting D=A[U,U^(-1)]/(t(U−1)) is exactly C_F, and B kills t, confirming that the argument must not assume A injects into B. Rank zero and nontrivial torsion among original units cause no failure. The deliberately nonmultiplicative a example above explains and tests the statement correction.

## Unfinished work

None in the natural-language split. No new unsplit tasks were introduced. Formal Lean implementation remains outside the authorized stage.
