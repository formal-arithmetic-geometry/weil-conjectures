## Files written

- dag/nodes/sec-trace-formula/lem-trf-trace-map-exchange.json: repaired stage-1 split, with its statement, statement dependencies, Lean audit and seven unaffected proof steps unchanged.
- dag/nodes/sec-trace-formula/lem-trf-compact-support-exchange-counit.json: new statement-only lemma; searched Mathlib, no match.
- dag/nodes/sec-trace-formula/lem-trf-relative-kunneth-counit.json: retained statement-only lemma from the interrupted attempt; searched Mathlib, no match. Added chapter/unit metadata.
- citations.json: 36 step/node entries, renumbered to the original nine-step proof and checked against the current statements.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the item tag and the notions trace/exchange/support, relative Kunneth/counit and proper/open/counit. ProperPushforward.lean defines coefficient pushforward and has the final borelMoorePushforward_traceClass theorem with sorry at line 312. It does not provide a sorry-free declaration of this item's three clauses. Neither new normalization lemma has an exact project declaration. Upstream master is reference material only.

## WANTED

None. The current blueprint proof and the operation/normalization source nodes needed here are present locally. No new SGA reference was used.

## Repair and retained work

The return singles out original steps 2 (3877 characters) and 3 (2744 characters). The previous interrupted attempt retained a relative Kunneth counit node and a ten-step version, but no report. I read its searches.jsonl and reused its searches and relative-product statement. I compared the sandbox with the current shared item and its retained nine-step returned proof. I kept the route and restored the seven unaffected steps exactly, including their original numbering. The item's statement and lean_audit compare equal to the current shared item. No Lean or live repository file was written and no compiler was run.

Original step 2 hid the equation relating compact-support exchange, the composition comparison, and the ordinary proper counits. That equation now has its own node lem-trf-compact-support-exchange-counit. The item still derives its last assertion: substitution in the conjugation formula gives one double transpose, and the new equation plus counit naturality gives the same transpose for the proposed composite. Thus the new node is neither the last assertion nor an exceptional base-change theorem in disguise: it contains no exceptional functor or exceptional adjunction at all.

Original step 3 hid the counit calculation for the specified inverse relative product. The retained lem-trf-relative-kunneth-counit isolates that calculation over an arbitrary separated finite-type base, with two independent proper maps and two arbitrary finite-Tor constructible inputs. Item step 3 still constructs its four product factors, applies that lemma, and substitutes the two external-product exchange transposes to get (**). Evaluation and support remain proved in the item. These are two smaller reusable comparisons, not new nodes for the item's evaluation/support clauses.

All nine non-elementary/elementary proof-step lengths are now at most 1381 characters (1347, 1214, 1381, 990, 912, 681, 1109, 957, 1019). I did not achieve this by relabeling non-elementary work elementary: the new application steps 2 and 3 remain non-elementary, and their hidden comparison arguments are named statements.

## Sources and intended arguments for the new nodes

I read literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-p-proper/lem-trf-trace-map-exchange.proof.md, all three paragraphs, and the chapter and sk-p-proper unit records. The last-assertion paragraph is the source of the new exchange/counit identity. The evaluation paragraph, from “Indeed Ku_!” through its displayed counit characterization, is the source of the relative-product lemma. Both nodes specify the actual geometric maps, finite ring A_{E,n}, separated finite-type schemes and the relevant constructible domains. Each new node has empty proof and proof_deps, no proof in its statement, no Mathlib match, and status unsplit; the arguments below are guidance for their future workers.

For lem-trf-compact-support-exchange-counit the intended route is the existing proper/open compactification route of the returned proof. For proper beta, expand the ordinary exchange as the unit--square--counit mate, use the adjunction-compatible direct-image composition, and transpose. Naturality brings the alpha-prime unit and counit together, so the ordinary triangle identity leaves the same pullback-square comparison followed by the counit on both sides. For open beta=j and beta-prime=j-prime, write gamma=j_! Ralpha-prime_* -> Ralpha_* j-prime_!. The Cartesian clause of lem-amb-unbounded-proper-open-interchange specifies gamma as the open adjunct of inverse ordinary exchange e, hence e j^* gamma=1. The ordinary exchange formula gives j-prime^* epsilon_alpha = epsilon_alpha-prime alpha-prime^*e. The open square exchange restricts to the identity by lem-trf-open-square-exchange. Restriction of both candidate maps is therefore epsilon_alpha-prime. Their common source is extension by zero, so the open adjunction, whose unit is invertible, identifies them. The finite etale proof transports with the named comparisons: def-cbc-finite-constant-coefficient-transport fixes the open comparison as a mate and lem-weil-pbc-comparison-direct-image-canonical-mate explicitly carries the ordinary counits to counits. The compact-support maps are the transported ones in fix-lem-exchanges. For beta compactified as proper after open, paste these two equations and cancel the intermediate composition comparisons; fix-lem-exchanges(2),(4) supplies pasting and refinement independence. This keeps Rbeta_!, with no claim Rbeta_!=Rbeta_* for nonproper beta.

For lem-trf-relative-kunneth-counit, I read the exact composite in thm-sf-kunneth-relative, the concrete definition in def-sf-kv-maps(i), and the proper compatibility of fix-prop-projection-formula. With H=Rf_*M and J=Rg_*N, the inverse relative product is the symmetric projection map for g, then Rg_* of exchange for f tensored with 1, then Rg_* of the projection map for q, followed by composition. Transpose first along g and then q. The first projection contributes the g counit on N; the middle exchange contributes p^*epsilon_f on M; the last projection contributes the q counit. The inserted units cancel against their matching counits by the triangle identities. Naturality and monoidal pullback then give p^*epsilon_f tensor q^*epsilon_g. The ordinary composition normalization of fix-prop-adjunctions(3) identifies this iterated transpose with the transpose along t. Proper identifications are justified because f,g and their base changes are proper. This statement is about the named inverse compact-support product, rather than defining another product by its transpose.

## Not duplicates

lem-trf-compact-support-exchange-counit vs lem-amb-unbounded-proper-open-interchange: the existing node supplies a proper/open comparison and its open-adjunction normalization; it does not state the ordinary proper-counit equation, and it only treats an open horizontal factor. The new equation treats arbitrary separated finite-type beta through compactification.

lem-trf-compact-support-exchange-counit vs lem-cbc-proper-open-interchange-coherence: that node supplies pasting and base-change equations for the proper/open comparison, not compatibility with the ordinary counits for alpha and alpha-prime.

lem-trf-compact-support-exchange-counit vs fix-lem-exchanges: exchange naturality, pasting and refinement compatibility do not themselves state the mixed counit/composition normalization (*).

lem-trf-compact-support-exchange-counit vs lem-trf-trace-map-exchange: the new node has no exceptional functor, dualizing object, correspondence, evaluation or support map. The item still uses two transposes to derive its last assertion from this equation.

lem-trf-relative-kunneth-counit vs def-kun-kunneth-map: that definition names the ordinary etale Kunneth map by the tensor-of-counits transpose; it does not identify it with the inverse of the specified compact-support relative-product composite.

lem-trf-relative-kunneth-counit vs lem-kun-kunneth-map-agrees: that theorem compares the absolute etale Kunneth map over a separably closed field with a projection/exchange composite under its specified Z or Z/n hypotheses. It does not give the relative geometric comparison over B with A_{E,n} coefficients.

lem-trf-relative-kunneth-counit vs thm-sf-kunneth-relative: that theorem specifies the composition/projection/exchange product and its isomorphism and base-change properties. It does not state its ordinary counit transpose.

lem-trf-relative-kunneth-counit vs lem-sf-kunneth-coherence: symmetry, associativity, base change and the identity-factor projection formula do not include the requested transpose identity for two proper maps.

lem-trf-relative-kunneth-counit vs lem-trf-trace-source-exchange: the existing statement is the kernel class comparison for coefficient pushforward. Its proof's product calculation is not part of its statement and cannot be cited as if it were.

I searched the whole DAG and imported blueprint with blueprint_refs.py searches for counit, exchange counit, relative Kunneth counit transpose, Kunneth, proper-open and trace-map-exchange, and keyword/normalization searches of dag/nodes. I opened the relevant candidate statements above, as well as lem-trf-ordinary-kunneth, lem-trf-adjoint-mate and lem-trf-cohomological-exchange-calculus. None states either new comparison. The new nodes have no Stacks source tag shared with an existing node. Blueprint ancestry is the item itself, via=[], with the precise source paragraphs recorded. No same_as match was found.

## Review by Q72

I checked the returned proof against the current blueprint and the actual statements of every dependency, not against their proofs. I checked the two new statements against the source paragraphs just identified and read the proper/open normalization nodes used by their intended route. The stage-1 repair keeps both auxiliary arguments available to future workers as independent statement-only items.

Step 1 uses def-trf-coefficient-pushforward for the finite coefficient stage and proper diagram; def-trf-admissibility for the specified constructible exceptional adjunction and adjunction-compatible composition; prop-functor-package for concrete operations and proper identifications; def-weil-pbc-adjunction-conjugate for conjugation and its composition law; and thm-sf-comp-composition for associativity of compact-support composition. The composite Hom bijections written in the step give the pasted exceptional counit. This avoids using the stronger ambient hypothesis of fix-prop-adjunctions(2).

Step 2 uses lem-weil-pbc-proper-base-change only to infer properness of alpha-prime, the new exchange/counit node exactly for (*), def-weil-pbc-adjunction-conjugate for the explicit formula and invertibility of the conjugate, and fix-prop-adjunctions(1) for the ordinary adjunction. After these citations the two displayed transposes differ only by naturality of epsilon_alpha; no unproved exchange/composition compatibility is being inferred from a definition.

Step 3 uses def-sf-kv-maps(i), which really defines the external product through the specified relative product and two exchanges; lem-weil-pbc-proper-base-change for a,b,r,t; the new relative-product node for its tensor-of-counits transpose; def-exchange-projection for the two ordinary exchange transposes; and prop-functor-package(7) for D_XK in the finite-Tor constructible domain. All four schemes are separated finite type. The two input exchanges have alpha-transpose pr_X^*epsilon_f, so substitution into the new relative formula gives precisely (**).

Step 4 uses def-weil-pbc-adjunction-mate for the general commutative-square ordinary mate, def-trf-kernel-pushforward-maps for mu_f, and fix-prop-adjunctions(1) for the ordinary Hom bijection. Its only other input is the preceding (**). It does not assume the diagonal square is Cartesian. The symmetry assertion is the written naturality equation for the tensor of the two counits.

Step 5 uses fix-prop-adjunctions(1) for the diagonal adjunction and def-trf-kernel-pushforward-maps for rho_f, delta_K and the tensor-Hom definition of chi_f. Once step 4 identifies the diagonal-pullback composite with mu_f, the displayed equation is the defining currying equation (with its stated symmetry). Cancellation of the isomorphism completes evaluation.

Step 6 uses prop-trf-fixed-square-cartesian for the two defining Cartesian squares, def-weil-proper-morphism for the separated diagonal condition, lem-pc-closed-subscheme-base-change-ideal-image for closed-immersion stability, lem-weil-pbc-closed-immersion-proper for properness, prop-functor-package(3) for star/shriek at these proper arrows, and lem-trf-fixed-map-proper for h and q. It asserts no properness of c,b,d_c,d_b or the structure maps.

Step 7 uses thm-trf-fixed-point-base-change and def-trf-kernel-pushforward-maps for the exact right-adjoint fixed-square comparison and its inverse zeta; thm-trf-dualizing-complex-composition for Rd_c^!omega_X=omega_Fc and the b analogue. Applying the last assertion proved in step 2 gives the two written exceptional adjoints. The proper alpha choices are the diagonals; the fixed-locus projections retain shrieks.

Step 8 uses def-trf-admissibility for the constructible b adjunction, def-trf-kernel-pushforward-maps for the defining transpose of E, thm-sf-comp-composition for the source identification and thm-trf-dualizing-complex-composition for its functorial dualizing comparisons. Inserting step 7 reduces the left side to the counit for fd_c by step 1.

Step 9 uses def-trf-kernel-pushforward-maps for tau_h and the right support arrow; def-trf-coefficient-pushforward for i_bh=gi_c and d_bh=fd_c; thm-sf-comp-composition for the associative source comparison; and thm-trf-dualizing-complex-composition for the functorial dualizing comparison. The two counits are those for the same morphism after these specified identifications, which is exactly the support conclusion.

I checked small cases of the new exchange/counit statement: alpha=id (both counits and Theta give the identity), beta=id (it reduces to epsilon_alpha), beta open (the restriction equation described above), and Z=0 or an empty fibre product (both arrows are zero). Beta=A^1_k -> Spec k is allowed and remains shriek, so no hidden properness hypothesis was introduced. For the relative-product node, f=g=id reduces to the tensor identity; one identity factor reduces to the counit-defined projection formula; zero inputs and empty products give zero maps; a proper finite disjoint union of points gives the expected sum on each tensor component. These checks distinguish the canonical product from an arbitrary isomorphism with a possible scalar/sign normalization. Koszul symmetry is kept in the specified derived tensor comparisons.

All citations.json quotes are actual substrings of the current cited statements (full statements are retained when needed to keep the hypotheses and map normalization visible). proof_deps is the union of the nine step uses. Off-unit generic geometry tools already accepted in the shared item are preserved; only the three still used geometry tool declarations remain in split_report.tool_uses. The new nodes stay in the item's own unit. There is no new assertion about integral or field coefficients, and no new statement dispute. The inherited blueprint prose incorrectly identifies Ex_! with Ex_* merely from proper alpha; the retained compact-support route corrects that by requiring a proper beta for that identification and handling open beta separately. It also retains Rd_b! in support when d_b is nonproper. These were already corrections in the returned proof, not changes of the item's statement.

## Unfinished work

Both new auxiliary statements intentionally remain unsplit for subsequent stage-1 work, as required for a one-level split. No part of the assigned item's natural-language proof remains pending. Server dry-run results and delivery are recorded by the required delivery command.
