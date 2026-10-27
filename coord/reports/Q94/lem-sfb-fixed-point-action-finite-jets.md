# Worker report: lem-sfb-fixed-point-action-finite-jets

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fixed-point-action-finite-jets.json: item split into eight explicit steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-point-thickenings-base-change.json: statement-only general geometric input, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-universal-fixed-subscheme.json: statement-only representability theorem, unsplit; no Mathlib match.
- citations.json: verbatim quotations for every step citation.
- searches.jsonl: actual msearch records; each new node records its own semantic, Loogle and source searches, including a second semantic phrasing.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag, finite jets, fixed subschemes, truncated local rings and actions at fixed points did not find a project declaration stating this item. The affine conjugation item lem-sfb-conjugation-finite-jet-kernel is a special case, not an attachment or a general-action substitute. Its affine-group comodule dictionary cannot be used for a possibly nonaffine H; this split uses Yoneda on all test schemes instead.

## WANTED

None. Milne and the relevant Stacks source files are available locally.

## Corrections and scope

No change to the statement, target, chapter or unit. The imported item contained no proof. Milne Proposition 8.9 uses faithfulness only after identifying the stable kernel as acting trivially. This delivery stops before that use. The appended errata, Chapter 8, p.150, explicitly requires reducedness in the fixed-subscheme argument; the item already assumes smoothness of X. I expanded the integral-domain argument instead of inferring scheme equality from equality of supports. No affineness, smoothness or connectedness assumption on H was introduced. The action convention on functions is pullback by the inverse action.

I read the current blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its sk-thm-sf-ctf-stability-direct-images.proof.md, especially proof (3). The item is far below that step through the existing Barsotti–Chevalley chain, and this delivery retains that route. blueprint_refs.py ancestor reports None for this inherited created-node chain; the new nodes preserve that ancestor and extend the existing via list.

## Not duplicates

Whole-DAG statement searches and blueprint_refs.py searches for fixed subscheme, fixed point, infinitesimal neighbourhood, rational point, local ring quotient, 04EY and 04EZ found no existing statement of either new lemma. The existing rational-point base-change maximal-ideal/stalk nodes concern field extensions and local rings, not arbitrary test schemes and the coordinate algebra of the finite thickening. The completion/Artinian-points node concerns maps from a completion, not this closed finite thickening or its arbitrary base change. The torus fixed-scheme nodes assume specified torus/linear actions, whereas universal-fixed-subscheme applies to arbitrary finite-type group schemes and separated schemes. The existing general-linear-group definition describes invertible matrices, not fixed-locus representability. The general affine conjugation kernel node is an application of this mechanism with substantially stronger hypotheses.

The searches found existing nodes for Krull intersection (lem-weil-pbc-krull-intersection-jacobson), schematic ACC (lem-weil-pbc-noetherian-acc-quasi-coherent), regularity and integrality; these are reused, with no new local-intersection, kernel-stabilization or smooth-connected-integral node. A Mathlib search found Ideal.iInf_pow_eq_bot_of_isLocalRing in RingTheory/Filtration.lean:432; reading it confirmed the local intersection fact, but the existing broader Jacobson-intersection node already supplies precisely what is needed.

## Review by Q94

I read Milne, Algebraic Groups, Theorem 7.1 and its proof on printed pp.138–139, Proposition 8.9 and Corollary 8.10 on printed p.150, and the appended erratum for that proposition. For the two new nodes I read, respectively, Proposition 8.9's finite-quotient/base-extension paragraph together with Stacks more-morphisms.tex's definitions and universal property of infinitesimal neighbourhoods (04EY, 04EZ), and Theorem 7.1's universally quantified fixed-point functor and its closed-subfunctor proof. The new nodes carry complete self-contained statements and empty proofs/dependency lists. Neither simply asserts that sufficiently high jets detect the action: that argument remains in the item's steps.

For step 1 I opened all four cited statements. The rational-thickening input supplies R, its residue field, finite-dimensional nonzero quotients and all base changes; the smooth-scheme regularity node states regularity without dimension restrictions; the regular-connected-integral node needs nonemptiness, provided by x; the finite-type-over-Noetherian node applies to H because Spec k is Noetherian. I read Stacks 056S, 0569, 033N and 01T6 at their labels. The cited regularity theorem is also visible in the project's Regular.lean. I did not compile it.

Step 2 uses the definition of a group scheme to form inverse automorphisms, the ideal-sheaf definition to preserve the kernel of evaluation at the fixed section, and the rational-thickening statement to identify the powers with T times Z_n. The equality T_(hh')=T_h T_h' has the inverse in the correct place. Since the construction works over every test scheme T, step 3 can apply the full Yoneda bijection, whose statement I read, to a transformation on Sch/k. I checked that the cited general-linear-group node gives matrices over arbitrary algebras and that V_n is nonzero so its dimension satisfies that node's c>=1 condition. No affine assumption on H enters.

For step 4 I opened lem-sc-kernel-subgroup and used its actual assertion K_n(B)=ker rho_n(B) and closed subgroup conclusion. Normality is the written conjugation identity, finite type follows on a finite affine cover by quotienting finitely generated algebras, and the decreasing-kernel argument uses the surjection already supplied by the thickening input. I read the closed-immersion ideal-factorization node: its statement says factorization is equivalent to inclusion of the defining ideals. This is schematic containment, never just containment on field-valued points. The ideal-sheaf definition explicitly supplies quasi-coherence.

Step 5 cites the ACC node's final maximal-element statement for quasi-coherent ideal sheaves, not a topological chain condition. This avoids hiding a structure-sheaf coherence lemma. I read its Stacks source 01Y8. A maximal member of the increasing sequence gives a single integer n_0, and the equality of ideals gives equality of schemes including their nilpotents. All lower-index kernels contain K as well. Triviality on each jet is tested as equality of morphisms on affine charts, so it holds universally, not just for k-points.

Step 6 uses the entire factorization clause of universal-fixed-subscheme to put each Z_n inside X^K. K is separated finite type as a closed subgroup of the given separated finite-type H; smoothness or reducedness of K is not needed by that theorem. The ideal-factorization lemma gives I_x inside every m^(n+1). I read the Jacobson-intersection statement: R is Noetherian by the rational-point-thickening lemma, the module R is cyclic, and the unique maximal ideal is exactly its Jacobson radical. Stacks algebra.tex, 00IP/00IQ, confirms these hypotheses. The existing Jacobson node already records the Mathlib result, so no duplicate was created.

Step 7 is the explicit elementary repair of the final density inference. In a nonempty affine of an integral scheme the coordinate ring is a domain; zero in a stalk is annihilation by an element outside its prime. This element is nonzero, so the local ideal vanishes already on that affine. Every other nonempty affine meets it by irreducibility; a nonempty principal open inside the intersection makes restriction injective by the same domain calculation. The cited ideal-sheaf definition says I is quasi-coherent and affine-local. Thus I=0, not merely radical(I)=0. The fixed-subscheme statement then gives equality of action and projection.

Step 8 uses the actual pointwise-kernel clause of the kernel lemma. One direction follows by arbitrary base change from equality of morphisms. In the converse the universal condition is tested on each affine chart Spec C of X_B, with B'=C and its tautological X-point; these equalities glue to the identity automorphism. Its inverse pullback on the jet is then the identity. I checked explicitly that neither this step nor the fixed-subscheme step discards nilpotent elements of B or B'.

Edge cases checked: X=Spec k gives V_n=k and K_n=H, agreeing with the trivial action kernel; trivial actions on positive-dimensional X again give K_n=H; a nontrivial infinitesimal subgroup acting on A^1 (for example mu_p scaling in characteristic p) is detected schematically by its scalar on the first jet even though its field-valued points may all be trivial; a nonaffine group acting trivially is permitted throughout. X cannot be empty because x exists, and V_n cannot have dimension zero because it surjects onto k. Positive characteristic was not excluded. Every proof step is under 2000 characters; none hides a longer auxiliary comparison. I checked delivery-errors B–E against the node files and read every cited statement, as quoted in citations.json. Off-unit generic tools are declared in split_report.tool_uses. No Lean or compiler/build command was written or run.

## Unfinished work

The two new inputs are intentionally unsplit stage-1 queue nodes, with complete statements, literature locations and actual Mathlib searches. The item's proof is complete relative to these and the cited existing nodes. No mathematical obstruction remains in the split.
