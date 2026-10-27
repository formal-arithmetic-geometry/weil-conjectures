# Stage-1 delivery: lem-sfb-reductive-torus-fixed-subgroup

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-torus-fixed-subgroup.json`: statement, split into seven proof steps using twelve existing nodes. No new nodes. No Mathlib match.
- `citations.json`: fourteen step/node entries, with literal excerpts of the cited statements.
- `searches.jsonl`: the actual Mathlib-search log produced by msearch.py. `write_split.py` records the sandbox-only preparation.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` both for the blueprint tag and for torus/centralizer/reductive terminology. The matrix centralizer equations in GroupScheme/GeneralLinear/ClosedSubgroup/LieSubalgebra.lean and the abstract subgroup centralizer in LinearAlgebraicGroup/Monodromy.lean do not state the smooth connected reductive group-scheme assertion. No Lean files were changed or compiled.

## WANTED

None: Milne's Algebraic Groups (2017) is available at `literature/milne-algebraic-groups_iAG2017.pdf`.

## Issues found and corrected

The mathematical statement agrees with Milne Corollary 17.59 and is unchanged. The inherited statement cited def-weil-field and def-weil-algebraic-closure without listing them in stmt_deps; both have been added. No STATEMENT-DISPUTED issue was found.

The inherited source specifically names 17.57, whose reverse-inclusion proof is the argument used here. Instead of assuming existence of the unipotent radical of C, we test an arbitrary smooth connected normal unipotent U. Its containment in all Borels of C is expanded on all test algebras, using an existing fixed-point theorem and the existing flag-variety statement. This avoids leaving an uncited assertion about normal subgroups and Borel subgroups. Chevalley's intersection theorem is used only in its existing first-equality form. The reduced identity component is essential, so the proof explicitly factors U through it before applying that equality.

The inherited blueprint.from.node is null, as confirmed by `tools/blueprint_refs.py ancestor`; its long existing from.place/via record is preserved rather than rewriting maintainer-owned ancestry. The latest blueprint snapshot is main-20261023-1620. I read its ctf-stability unit and direct-images proof (3), and the inherited ancestor det-thm-sf-ctf-stability-direct-images. This is an algebraic-group prerequisite far below that route, not a change of its cohomological argument. Whole-blueprint searches for centralizer, torus centralizer, unipotent, and Borel intersection found no matching statement. The three centralizer hits concern characteristic-zero geometry/Cartier reducedness, not this arbitrary-characteristic torus-centralizer theorem.

## Not duplicates

No new nodes are proposed. In particular the existing smooth-connected centralizer, Borel-intersection and Chevalley-intersection nodes are reused, not restated as new leaves.

## Review by NU

I read Milne Corollaries 17.57 and 17.59 and Theorem 17.56 on printed p.371, and the smoothness and connectedness inputs 13.9--13.10 and 17.38. The item is exactly the centralizer case of 17.59; it does not require S to be maximal and works in every characteristic. I also checked the normality/fixed-point expansion against the existing statements of the flag-variety and fixed-point nodes. There are no new nodes requiring independent source review.

For step 1 I opened lem-sfb-multiplicative-type-largest-subtorus, which explicitly says every torus is smooth and connected, and lem-sfb-solvable-normal-subgroup-products, which gives integer dimension bounds and strict dimension increase for proper smooth connected subgroup inclusions. These statements justify choosing a maximal torus above S by greatest dimension. The latter bound is stated for subgroup schemes, not only the normal solvable subgroups discussed earlier in that node. The argument does not assume a maximal torus containing S without justification.

For step 2 I checked lem-sfb-torus-centralizer-smooth-connected. It assumes only a smooth geometrically connected affine finite-type G and any torus. Those hypotheses follow from reductivity over the algebraically closed F. Its centralizer condition quantifies over arbitrary test algebras and further extensions, exactly as the item does, and it supplies closed representability as well as smoothness and connectedness.

For step 3 I read lem-sfb-smooth-unipotent-solvable, including its geometric-matrix interpretation, so it applies to the arbitrary smooth unipotent U in the reductivity definition. I read lem-sfb-general-borel-flag-variety: it supplies a nonempty proper finite-type flag scheme for the smooth connected C, its group action, its rational points indexed by Borels, and its scheme-theoretic stabilizers. The hypotheses of lem-sfb-solvable-proper-fixed-point are therefore satisfied by U and this scheme over the algebraically closed F. This is a fixed point after every algebra extension, not just an F-pointwise assertion.

For step 4 I used precisely the transitivity and all-algebras stabilizer clauses of the same flag-variety node. The displayed conjugation calculation uses normality of U in C after arbitrary base extension, showing U is a subgroup of every Borel of C. No scheme equality is inferred merely from equality of rational points. This is a short direct calculation from the cited flag statement and the fixed point already obtained, not a newly postulated lemma.

For step 5 I opened lem-sfb-torus-centralizer-borel-intersection. Its hypotheses are smooth connected G, a Borel B and a torus S contained in B; these hold because S is contained in T and T in B. Its conclusion states exactly that C cap B is a Borel of C. The universal property of a sum of ideals then gives U inside the scheme intersection I. The argument does not use any reductive root datum or later rank-one result.

For step 6 I read sbc-lem-smooth-geometrically-reduced and lem-weil-pbc-reduced-source-factors-through-closed-subscheme. Smoothness of U over the field gives reducedness; connectedness and the identity put its image in the identity component. The reduced-source factorization statement applies twice to the specified closed subschemes. I read lem-sfb-chevalley-borel-intersection, which states exactly the reduced-identity-component equality with R_u(G) times T, not an equality with the whole intersection. I checked the definition of reductivity in def-sfb-reductive-torus-centralizer-terminology: it kills R_u(G) because the latter is explicitly smooth connected normal unipotent in the Chevalley node. Thus U factors into T scheme-theoretically.

For step 7 I read lem-sfb-unipotent-to-multiplicative-trivial. It explicitly identifies the smooth matrix notion with its unipotent group-scheme notion, and says every homomorphism to a multiplicative-type group is trivial on all algebras. T is a split torus, hence multiplicative type, so its application has all hypotheses. The closed inclusion U into G remains a monomorphism, forcing U to be trivial as a group functor, including over nonreduced algebras. The reductivity-definition node then gives the conclusion over the already algebraically closed field.

I checked B--E of delivery-errors against these files. The only written node is the item; statement-only rules for new nodes are vacuous. Each dependency actually states the part used, with a verbatim quotation in citations.json. No dependency cites its proof in place of its statement. All non-elementary inputs are named nodes, the elementary steps give their dimension or conjugation calculation explicitly, and no step exceeds 2000 characters. No SGA source is used. The proof keeps both reducedness and connectedness at the intersection step and excludes only smooth connected normal unipotent subgroups, not arbitrary finite infinitesimal subgroups.

Small cases checked: S=1 gives C=G and the same intersection argument; S maximal gives a torus centralizer without assuming that stronger result; a central S gives C=G; G a torus and the rank-zero trivial group both satisfy the proof. In positive characteristic a subgroup such as mu_p is not a smooth connected unipotent U; the proof never treats geometric-point triviality as subgroup-scheme triviality. This checks the main possible characteristic-p pitfall.

Mathlib searches were run through msearch.py only, in two semantic phrasings plus LeanSearch, Loogle and two source greps. Hits were abstract fixed subgroups and centralizers, or Cartan/radical theorems for Lie algebras. None concerns affine algebraic group schemes. In particular characteristic-zero Lie algebra results cannot establish the arbitrary-characteristic group statement. The inherited searches are retained and the newly run queries are appended exactly as logged.

## Unfinished work

None in this one-level split. The twelve cited proof nodes remain their own work items according to live state; no new queue items are introduced. Required server dry run and push results will be recorded below.
