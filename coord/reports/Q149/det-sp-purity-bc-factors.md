# Stage-1 report: det-sp-purity-bc-factors

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-purity-bc-factors.json`: existing eight-step item retained, status set to split, Q149 report and actually logged Mathlib searches recorded.
- `citations.json`: all 53 proof-step citations, each with the verbatim cited statement.
- No new nodes and no Mathlib leaves. The interrupted root-level item copy and search log are retained.

## Attachments

None. I searched the specified read-only source checkout for the blueprint tag and purity/orientation base-change terminology. `Basic.lean:453`, `leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom`, uses the purity-defined exchange (its definition expressly distinguishes it from the compact-support mate). It therefore does not prove either requested factor identity for the specified counit mate. `Orientation.lean:225,277` treats the affine-line supported orientation, not all smooth morphisms, tensor maps, and varying-coefficient towers. No exact attachment was found. No upstream master sorry is used as proof evidence.

## WANTED

None.

## Findings and changes

The interrupted sandbox held an exact copy of the current repository item, including an inherited review, but no report, citation manifest or node-directory layout. I retained its mathematical proof and statement, placed the delivery copy in the required node directory, supplied this report and the citations, and marked the completed one-level split. I did not create or set a new maintainer review. The inherited review and accepted-tool metadata are retained from the base rather than claimed as Q149 review authority.

The first server check refused the missing node-directory layout; the next server check exited with “the sandbox holds no change against origin”. It had checked the unchanged copy before the split status/report edits. These are delivery-preparation failures, not mathematical claims. The final deliver dry run is the authoritative preflight.

I read the chapter and unit records, the current main-20261015 `sk-prop-sp-purity-bc/_section.md`, the factors statement and its proof, and compared the item's two factors and final composite. The proof follows the diagonal/DNC/vector-bundle route and the counit-transpose route. It cites no SGA. The item is not the unit's key statement, so the unit record is untouched. No statement dispute or route replacement is needed.

The saved Mathlib log was read and reused: projection/base-change, diagonal dualizing comparison, finite-Tor pullback and purity searches have no matching theorem. The semantic hits concern ordinary algebraic base change, smoothness or module pullback; the Loogle adjunction/pullback query returned no hit. I replaced inherited search entries absent from Q149's log with exact tool/query pairs actually present there. The invalid `CategoryTheory.Limits.IsPullback` query is retained with its reported unknown-identifier result; the corrected `CategoryTheory.IsPullback` query also ran and returned no hits. No unavailable service is called a negative result.

## Review by Q149

I opened every cited node and read its statement. The citation manifest copies statements verbatim, not a proof or an inferred replacement statement. I checked the finite ring, tower, uncompleted tensor, uniformly bounded finite-Tor and counit-mate conventions separately. Arbitrary base change remains arbitrary; normalization, flatness of the base-change map and unramifiedness of E have not been introduced.

Step 1 uses the actual diagonal comparison of `lem-pur-diagonal-base-change`, not a generic existence isomorphism. `fix-lem-exchanges` explicitly gives both pasting laws, and `lem-weil-pbc-mate-pasting` gives their exceptional mates and identity normalization. I checked the displayed cube equation and its pullback along the diagonal: both sides become maps from the same section invariant to the primed dualizing object. The smooth-relative-dimension permanence and regular closed diagonal statements supply precisely their respective geometric hypotheses. The finite-Tor comparison supplies etale-origin witnesses because R is discrete Noetherian and these schemes are quasi-compact quasi-separated.

Step 2 uses the arbitrary-base-change clause of DNC invariance for the smooth closed-section pair (W -> X, diagonal), and the geometry node explicitly identifies the two fibers and permits base change. The diagonal normal bundle has rank d by the regular-diagonal statement. Vector-bundle purity expressly commutes with base change and adjunctions. The orientation-charts statement spells out the diagonal composite and fixes its normalization at R=Z/l^r; it is not applied directly to arbitrary A. I checked the direction Pi: omega -> twist and the inversion to a: twist -> omega.

Step 3 uses clauses (1)-(2) of `det-sp-finite-general-ring` for the scalar-extended and direct diagonal constructions. The mixed exchange equation is an explicit assertion in `lem-pur-dnc-coefficient-transport`, with any finite coefficient ring B, not merely a quotient residue field. The derived tensor/pullback statement supplies the source comparisons. The cancellation is by an isomorphism. For ramified E, O_E/l^n is A_{E,en}, so the argument uses the correct index.

Step 4 uses actual tower orientation and exceptional exchange morphisms from the tower-gamma and tower-exceptional-bc statements. `det-sp-coefficient-towers-abelian` provides exact evaluation, and the derived single-complex lemma provides full faithfulness only for degree-zero sheaves. Removing the common shift makes h a map of the Tate sheaf tower; the definition of towers makes its componentwise identity imply identity. No faithfulness of evaluation on general derived Hom sets is used.

Step 5 uses the inverse-system-topos description in the tower-abelian statement, then the generic ringed-topos exchange/tensor coherence statement in that topos itself. It applies to a commutative ringed-topos square, without requiring the square to be Cartesian. The open part is proved by restriction under the exact open adjunction: the two composites have extension-by-zero source and identical restrictions, so the Hom adjunction detects equality. The finite open-extension, open-base-change and open-projection statements give the three specified maps; the tower shriek calculus gives the actual tower open adjunction. The tower-shriek-levels statement supplies the compactification maps and their witness hypotheses. Finite-Tor comparison supplies those witnesses level by level; no compatible tower of chosen witnesses is required. Finite-general-ring(3) and tower-gamma(2) give the invertibility of the projection maps used with omega. The definition of exchange/projection supplies the proper-then-open formulas; its residue-ring scope is explicitly respected by using the same ambient ringed formulas for arbitrary A.

Step 6 checks the adjunction domains before transposing. The finite-level Tor-pullback statement applies to A_{E,en} and gives the same common bounds at all levels; exact pullback preserves the common cohomological interval. The definition of uniform towers and tower-gluing then give the claimed domain. For arbitrary finite A the flat-model statement actually covers such A, the bounded-flat lemma makes the model K-flat, and the ringed-pullback lemma preserves that property with flat terms. Exact constant-coefficient pullback is explicitly stated in `def-weil-pbc-proetale-operations`. Pulling back the finite stratifications and the local constant models verifies the constructibility definition directly. The bounded complex computes tensor with a sheaf in a finite interval. These checks do not assume coefficient reduction is flat.

Step 7 uses the stated mate definition, the tower exceptional counit transpose, and the finite/tower tensor-map transposes. I recomputed the displayed equalities: naturality of beta changes beta_GK^{-1} F'u*t into v*F(t) beta_P^{-1}; projection/base-change coherence then produces the pulled-back unit counit, which the unit mate identity changes to epsilon'_1 F'e_1. Naturality of the inverse projection map gives the final transpose. The tower-gluing Hom bijection detects equality in the tower category itself. Step 8 substitutes the two proved factor equalities into the exact gamma definitions; monoidal pullback preserves the twist reassociation. It proves the consequence without assuming it to establish a factor.

I reviewed the three long steps (1, 5, 6). Each expands the application/domain check of cited general lemmas and includes an explicit routine calculation: diagonal cube pasting, proper/open compactification composition, or bounded flat-model pullback. None hides an uncited independent lemma. I retained them rather than creating duplicates of the cited statements or nodes restating the item's clauses. No new nodes exist, so B1-B9 and duplicate checks for new nodes are vacuous; for the item all notions are introduced and their definition dependencies retained. The proof dependencies equal the union of uses. Generic off-unit tools are declared in the inherited split report and serve the stated route.

I read Stacks tags 07A4 (`lemma-pullback-tensor-product`) and 0E48 (`remark-compatible-with-diagram`) in `sites-cohomology.tex` for the tensor and exchange square, and checked their tag-label mapping; 06XS is the degree-zero derived-Hom reference underlying the existing full-faithfulness node. These sources support the generic tools, while the item's proof origin remains agent-written from the blueprint. No source is represented as a verbatim theorem when it is an assembly.

Small cases checked: identity f and identity v reduce the mates and factors to identities; d=0 removes twist and shift; empty schemes and the zero finite ring give zero categories, where the displayed identity morphisms remain valid; nonflat v is allowed by smooth-section DNC base change; ramified E uses en; nonnormalized towers use only uniform bounds and componentwise sheaf equality. None reveals a missing hypothesis or a weakened conclusion.

## Unfinished work

No mathematical work remains in this one-level split. Direct delivery and independent maintainer review are the remaining process steps.
