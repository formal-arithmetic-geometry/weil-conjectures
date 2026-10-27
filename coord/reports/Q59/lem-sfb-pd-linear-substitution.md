## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pd-linear-substitution.json — statement split; unchanged statement, five explicit finite-sum proof steps, no exact Mathlib match.
- citations.json — one verbatim quotation for every node in every step's uses.
- searches.jsonl — five actual Q59 search results, supplementing the inherited Q10 searches retained in the item.

No new nodes and no new Mathlib leaves. The binomial theorem is already lem-pur-commutative-ring-binomial-expansion; ordinary divided powers are already def-sfb-ordinary-divided-power-structure.

## Attachments

None. Searched lean/WeilConjectures and lean/Sheaf for the exact item id, linearSubstitution, linear_substitution, dpow_linearCombination, pdLinear, DividedPowers and divided-power terminology. There is no project declaration of the matrix identity. The Lie-theoretic divided-power declarations concern a different construction.

## WANTED

None.

## Corrections and source comparison

The statement is correct and has not changed. The imported node had no proof. Stacks dpa.tex, Tag 07H1 (lemma-gamma-extends), contains precisely the displayed matrix identity in the flat-case paragraph. Flatness is used only afterwards for the common-refinement argument, not for this identity. Our proof supplies its coefficient-expansion details directly over B, without invoking the rational universal-coefficient comparison. It is therefore marked agent-written, with the source paragraph identified. This is the same binomial/divided-power expansion, organized as finite coefficient arrays.

The current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md put this deep supporting chain below direct images, clause (3); they do not state this matrix identity. The inherited ancestry resolver prints None and is retained, with its detailed place and via list. Blueprint-wide searches for “multinomial”, “divided power”, and “linear substitution” found no statement duplicating the item; the last query's integration-along-a-vector-bundle hit concerns trace gluing, not divided powers. DAG searches for 07H1 and divided-power/binomial terms were read: the flat-extension and polynomial-extension nodes use this identity, rather than providing an independent proof. The existing commuting-binomial node requires a field algebra and cannot be applied to arbitrary B; the commutative-ring binomial node has exactly the hypotheses needed.

Mathlib searches were run by msearch.py (all services available). Read Basic.lean:259–270 and 329–351. prod_dpow and dpow_sum are useful source-ring expansions, but neither gives the matrix identity. dpow_linearCombination requires a divided-power structure on the ambient target ring; DPMorphism results require target divided powers too. A second semantic phrasing confirmed this distinction. The inherited searches and their results were retained, not claimed as new Q59 calls.

## Unfinished work

None for this stage-1 split. No Lean was written or compiled, and the repository and launcher were not edited. Validation and delivery use only the required server-side tools.

## Review by Q59

I read dpa.tex Tag 07GL (definition-divided-powers, the five displayed axioms) and Tag 07H1 (lemma-gamma-extends, especially the matrix-substitution paragraph), then reread both cited DAG statements. For the existing binomial leaf I checked algebra.tex Tag 0545 (lemma-help-with-powers, its binomial expansion) and Mathlib/Data/Nat/Choose/Sum.lean:75–78, where add_pow is stated for every commutative semiring; B is a commutative ring and satisfies this hypothesis. No new node requires a source audit.

Step 1 uses no theorem beyond finite distributivity: the triple-index sum proves associativity explicitly, swapping the pair proves commutativity, and induction on the number of factors proves the displayed coefficient formula. All indices are at most n, so these are finite sums, with no convergence or power-series construction assumed. These are elementary calculations, not new lemma nodes.

Step 2 uses def-sfb-ordinary-divided-power-structure exactly for its scalar axiom and zeroth-power convention. Setting its scalar to zero proves gamma_m(0)=0 for positive m; degree zero is handled separately. Both E(0;t) and E(z;0) have entries (1,0,...,0).

Step 3 uses lem-pur-commutative-ring-binomial-expansion for (t+u)^m and the ordinary divided-power definition for the binary product identity. The quotation from each statement supplies precisely that formula. The definition states the product axiom for positive indices, so I explicitly checked the cases p=0 or q=0 with gamma_0=1 and binomial endpoint 1, including m=0. Applying f preserves integer coefficients because f is unital. There is no cancellation of factorials or assumption on the characteristic.

Step 4 uses only the addition and scalar formulas literally stated in the ordinary definition. The degree-m calculation includes the factor t^(p+q)=t^p t^q, and the scalar calculation uses f(a^m)=f(a)^m. Degree zero is again 1 on both sides. The ideal hypothesis ensures z+w and az lie in I.

Step 5 uses the already proved elementary steps, with an explicit base and successor for each finite-sum iteration. For the row expansion, t_j=f(a_ij)c_j is any element of B, as step 3 allows. For the column expansion, a_ij x_i belongs to I, as step 4 requires. The row and column products have exactly the same rs factors; step 1 permits their reordering. Its nth-entry formula is exactly the two P_n expressions, so this proves the full item, not a renamed clause. No off-route non-Mathlib statement is invoked.

I tested n=0 (both sides 1), r=0 and s=0 (the relevant arrays and all empty products are delta), n>0 with a zero ideal, zero rows or zero coefficients, and the one-row/one-column case (the scalar axiom). At n=2 the mixed term is correct because 2 gamma_2(x)=gamma_1(x)^2, including characteristic two; no division by 2 occurs. Since all calculations are identities preserved by every ring map, noninjective and nonflat maps need no extra hypothesis. There is no statement dispute.

Against delivery-errors B–E: no duplicate, elementary, clause-restatement, or unsearched new nodes were introduced; all objects in the unchanged statement remain explicit; every non-elementary external ingredient is the existing binomial leaf, whose statement was checked. Every citation has a verbatim quote in citations.json, and proof_deps is exactly the union of uses. The dependency graph points only to the ordinary definition and existing binomial leaf, neither to a descendant using this item. No step exceeds 2000 characters (the longest is under 900), and every step is a finite calculation or a two-line consequence of its cited formulas. No SGA route is used.
