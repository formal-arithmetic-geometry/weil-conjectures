## Files written

- `dag/nodes/sec-six-functors/lem-coef-monoidal-square-hom-transport.json`: statement, split into eleven explicit categorical calculations. Full-item Mathlib verdict: no match; cartesian exponential comparisons do not specialize to general symmetric tensor categories.
- `citations.json`: verbatim statement quotes for every cited node in every step.
- `searches.jsonl`: actual Mathlib search-command results, retained with tool/query/digest in the item.

No new nodes, no new Mathlib leaves, no unit file changed. The item's statement and original source record are unchanged.

## Attachments

None for this item. I searched the slopmaster2 `WeilConjectures/` source by the exact blueprint tag, the item id, monoidal-square terminology and internal-Hom-comparison names. The project file `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean` has genuine sorry-free component results: `CategoryTheory.Functor.LaxMonoidal.ihomComparison_ev` (118), `ihomComparison_comp_app` (259) and `ihomComparison_app_comp_map_app` (271). They state evaluation, composition of two functors, and compatibility with a monoidal transformation, respectively. No one of them, or their conjunction, states the full item: it additionally asks for both-variable naturality, all transpose and internal-composition compatibilities, and coherent transport through two coefficient squares. Therefore I did not claim ATTACH for a partial declaration or use an unrecorded project theorem as a black box. The short component calculations are written out in the proof instead.

## WANTED

None. The blueprint source, Stacks categorical definitions and the Mathlib uncurry source were available locally. No SGA source was used.

## Audit findings and repairs

The unsplit item was already a correctly scoped extraction of the final site-comparison sentence of `thm-coef-finite-hom`. It explicitly assumes strong symmetric monoidal functors and invertibility of the two site comparisons at the relevant pairs; it does not assert essential surjectivity. Its displayed equations suppress the endpoint map induced by the natural isomorphism h. I made that map explicit in the proof as `r_h = H(h_K^{-1},h_M)`; this is a clarification of its existing “after identifying” convention, not a statement change.

The source proof says that associativity and uniqueness of transpose give the compatibilities. The new steps expand those words: the square equation has two evaluated expressions with identical source; internal composition has two successive evaluations; coefficient composition has explicit cancellation of the middle beta and the naturality/coherence formulas for h. The parent source record remains the older master blueprint location; I also read the main-20261015 statement and separate proof at `sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.{md,proof.md}`. These have the same final categorical argument. I retained the item's maintainer-owned chapter/unit binding and its historical blueprint ancestry.

The current chapter and unit records were read: `sec-six-functors` and `sk-prop-sf-biduality-general`. This item is not a unit key statement. Its calculation serves the finite coefficient transport within the existing route, and does not replace any geometric or duality step.

## Not duplicates

No new nodes were created. Before deciding this I searched the whole DAG statements for internal-Hom comparisons, monoidal natural transformations/isomorphisms, transpose/uncurry laws and project declaration names; I searched the whole imported blueprint with `blueprint_refs.py search` for evaluation, monoidal, internal-Hom comparison and the exact item title. `lem-pod-closed-uncurry-laws` was reused. `thm-sf-hom-comparison-constructible` and `lem-sf-hom-comparison-finite-free` are site-specific comparison theorems, not the abstract square identity. The former is an application-level input rather than a replacement for the present calculation. No blueprint node states the full item in another form, so `same_as` stays empty.

## Review by Q113

I read the original master `thm-coef-finite-hom` statement and proof, the main-20261015 version and separate proof, the full statements of `def-nagata-category`, `def-sfb-monoidal-category` and `lem-pod-closed-uncurry-laws`, and Mathlib `CategoryTheory/Monoidal/Closed/Basic.lean` lines 140–205. I checked Stacks `categories.tex`, definition-monoidal-category (Tag 0FFK), for the associativity/unit convention; the existing definition node uses the inverse Stacks associator so it has Mathlib's orientation. I also read the project's component comparison proofs at the lines listed above. No unavailable literature or omitted standard theorem is being used.

Step 1 uses the uncurry node's stated adjunction bijection, its cancellation, precomposition and evaluation formulas. Since it uses tensor-left and our item tensor-right, the step explicitly precomposes by symmetry. This is a bijection and preserves injectivity. The monoidal-category node supplies the tensor bifunctor, associator, naturality and coherence convention, not a claimed comparison theorem. Formula (E) is the item's definition of v uncurried, so no preservation theorem is assumed.

Step 2 uses the same uncurry formula to characterize H(h_K^{-1},h_M). Its direction is crucial: H is contravariant in K and covariant in M, so h_K must be inverted and h_M must not. I checked the two-sided inverse by functoriality. The resulting equation (S) has source U_B F H(K,M) and target H(G U_A K,G U_A M); the original displayed formula is exactly it after the allowed endpoint identification.

Steps 3 and 4 cite those same uncurry and tensor axioms. I checked each equality: (E) is used once for each functor on the corresponding side, tensorator naturality moves the beta, the composite tensorator is G(mu_U) mu_G or U(mu_F) mu_U, naturality of h at evaluation gives the penultimate equality, and monoidality of h gives the final equality. Their sources are both U_B F H(K,M) tensor U_B F K. Cancellation of the invertible h_K followed by injectivity proves (S). No equivalence of categories or invertibility of v is used.

Step 5 uses only the category node's associativity, identities and inverse definition, and functoriality explicitly assumed for the functors. Composing on the right cancels G(beta_A) against G(beta_A^{-1}) in the correct order. It keeps r_h, then suppresses it only under the statement's endpoint convention. Invertibility of v_G is obtained only with invertibility of v_F as input.

Step 6 uses the uncurry node to compare the two inverse transposes of (N); the tensorator's naturality and the definition of H(a,b) give the displayed common pairing. I verified a:K'->K is contravariant and b:M->M' covariant. Naturality of beta and of r_h follows from this written calculation and the assumed naturality of h, not from an unavailable sheaf theorem.

Step 7 uses the same evaluation/precomposition formula for a general test map t. Equation (T) is obtained in two substitutions, and is exactly the preservation of the specified tensor-Hom transpose. I checked the square version by the two explicit naturality/monoidality equations for h at t and T tensor K. It compares actual pairings, so it does not just identify endpoints.

Step 8 uses the monoidal associativity axiom and the uncurry evaluation formula. Internal composition is defined in the item to have the stated two-evaluation inverse transpose. Both sides of (C) have source V H(L,M) tensor V H(K,L); after tensoring with V K the two applications of (E) give the same double evaluation, with the same associator. No dualizability or closedness-preserving assumption on V has been added.

Step 9 applies that same calculation to the site comparisons, and formula (H) twice to r_h. The h_L and h_L^{-1} cancel between the successive evaluations. The beta inverse factors used for conjugating the equation exist at precisely the relevant pairs in the hypothesis. I checked that this is an equation on image pairs and never uses fullness, faithfulness or essential surjectivity.

Step 10 evaluates the composite comparison and writes the composite tensorator in full; injectivity proves (P), and the identity case is its own one-line evaluation calculation. This is an elementary calculation from definitions, not an extracted node restating a clause of this item. The monoidal composite-isomorphism case follows from the already proved square calculation with identity vertical functors.

Step 11 gives the cancellation calculation rather than saying only “transport coherence.” I checked the middle beta is evaluated at (F_AB K,F_AB M), so its two occurrences really are inverse arrows before G_BC is applied. Naturality of h_BC is written for the actual arrow a=v_FAB. The residual h factors are exactly the coherent h_AC from the hypothesis, and H functoriality deals with their two endpoint factors. Thus suppressing endpoints in this one calculation does not assume a strictification theorem. The F composition identity is used only at the last equality. The identity equation similarly cancels beta_A beta_A^{-1} with the specified identity comparisons.

For delivery-errors B–E: no new-node shape, duplicate-tag, disguised clause or Mathlib-leaf claim arises. Each citation is to the statement just described, never to a proof or to a definition pretending to assert a theorem. All remaining facts are the displayed short functoriality, naturality, inverse-cancellation or inverse-transpose calculations from the hypotheses. There is no hidden geometric or homological lemma. All eleven steps are below 2000 characters (the longest is step 11, 1539); I reread it for an implicit comparison lemma and found its comparison and cancellation equations explicitly present.

I tested the scope on identity functors and identity h (S reduces to the composite-comparison equation), on nontrivial h (the first-variable inverse in r_h is forced by evaluation), and on zero objects/zero pairings in module tensor categories. The argument never cancels an evaluation, a tensor functor or a noninvertible comparison; it cancels only h or an assumed beta inverse and uses the adjunction bijection. Hence these small cases do not require a nonzero object or invertibility not supplied by the statement. I also checked empty categories: the assertions are quantified over their objects, so there is no extra existence requirement. General vector-space/module tensor provides a check that the rejected cartesian Mathlib candidates really impose an extra hypothesis.

## Unfinished work

None in the mathematical split. Required remote dry run and direct delivery follow; their results are reported by the delivery command.
