# Stage-1 delivery: lem-sf-perfect-pairing-reduction-adjoints

## Files written

- `dag/nodes/sec-six-functors/lem-sf-perfect-pairing-reduction-adjoints.json`: statement, now split into six proof steps; no full Mathlib match.
- `citations.json`: one verbatim statement excerpt for each node cited in each proof step.
- `searches.jsonl`: actual wrapper search records, retained unchanged.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. Reused `lem-pod-closed-uncurry-laws`, an existing Mathlib leaf. No Lean was written or compiled; all writes are in the assigned sandbox.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint tag gave no hit. Searches for perfect pairings, pairing adjoints and evaluation comparisons found module-specific Poincare and Frobenius pairings, and the general closed-category comparison interfaces in `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean`. None states all the clauses of this item with arbitrary evaluation-normalized h and arbitrary r.

## WANTED

None. The blueprint proof, Mathlib sources and Stacks category definitions needed here are available locally.

## Issues found and repaired

The item was statement-only and had no proof. Its statement is correct and unchanged, including the dual of c inverse and the absence of any invertibility assumption on r. Its imported source calls the last paragraph the second paragraph, although the Markdown is laid out continuously; the split source identifies the exact sentences instead. No mathematical route or statement dispute was found.

The earlier searches in the live node were retained as inherited evidence, not represented as searches by Q148. Seven additional actual wrapper searches are appended with their exact query strings and complete logged summaries. The second LeanFinder process lost its terminal session after a provider interruption, but `searches.jsonl` records its completed eight-hit result; I read that result rather than repeating it. The main additional candidates were generic rigid exact-pairing triangle identities, Cartesian closed exponential comparisons, enriched internal-Hom composition, and adjunction transforms of commutative squares. Those do not state this item. The existing uncurrying leaf supplies the actual common ingredient.

## Unfinished work

None in this one-level split. There are no new unsplit dependencies. Maintainer independent mathematical review remains the normal next stage.

## Not duplicates

No new nodes were created. The existing uncurrying leaf was reused instead of adding a second version; no statement was moved to a new node or restated as an auxiliary clause.

## Review by Q148

I read the item and its entire statement, the `sec-six-functors` chapter record, the `sk-thm-sf-package` unit statement and assembly proof, and the current blueprint `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-finite-reduction.proof.md`. The last paragraph explicitly takes adjoints in the commuting pairing square and then inverses of horizontal adjoints. This split supplies exactly that formal step. The blueprint supplies the route, and I wrote the explicit algebra, so `proof_origin.by` is `agent`. No geometric or coefficient theorem is being assumed here, and no SGA source is used.

I read the statements of every cited node, rather than their proofs. I also read the pinned Mathlib `CategoryTheory/Monoidal/Closed/Basic.lean` lines 140–203 and 230–280: the adjunction equivalence, evaluation formula, inverse cancellation and precomposition formulas agree with the conventions in the item. The reused leaf `lem-pod-closed-uncurry-laws` states uncurry(curry(u)) = u and the evaluation formula for every v. Its adjunction hypotheses are precisely available in each of the two categories in this item. For the two definition nodes I read their complete statements and their source in `literature/stacks-project/categories.tex`, Tag 0FFK (`definition-monoidal-category`) and Tag 0FFL (`definition-functor-monoidal-categories`), including functoriality of tensor and tensorator naturality. There are no new-node sources to check.

Step 1 cites the uncurrying leaf for both actual evaluation identities. Injectivity here is just the injectivity of the inverse of the bijection already in the hypotheses. Step 2 cites the monoidal-category definition for tensor bifunctor composition; it writes the defining transpose of precomposition, derives its composite and identity laws by uniqueness, and checks the two inverse composites of the dual of c inverse. It does not silently use a dualizability theorem or infer an isomorphism from an exact pairing. Step 3 uses only that same tensor composition law and the assumed evaluation equation for h, yielding the required equation with c and ell and the correct unit constraint.

Step 4 cites the monoidal-category definition for composition of tensor maps and the strong-monoidal-functor definition for exactly the naturality formula with f = identity of C and g = b. I checked its types: mu(C,C dual) after (identity of FC tensor F(b)) equals F(identity of C tensor b) after mu(C,D). Both evaluated maps have domain FC tensor FD and target the unit of D. Step 5 cancels c tensor identity using its explicitly written inverse; only then does the uncurrying leaf and the hypothesized bijection give equality of maps FD to (C prime) dual. Step 6 uses functor preservation of identity and composition, stated in the strong-functor definition, to exhibit both inverse identities for F(b); composition with the assumed inverse of b prime gives the inverse-adjoint square and both inverse identities for r. The cited verbatim excerpts are in `citations.json` for every step/node pair.

I checked the B–E delivery-error cases individually: all objects and adjunctions are introduced in the unchanged statement; proof dependencies are exactly the union of uses; no definition is cited for an unstated theorem; all non-elementary input is the existing uncurrying leaf; the remaining steps write short equation calculations from definitions and the item hypotheses. No new node is elementary, a duplicate, or a clause of the item because there are no new nodes. No step exceeds 2000 characters. Dependencies go only to existing Mathlib leaves, so there is no circular appeal to the parent reduction theorem and no off-unit theorem route change.

For small cases I checked the identity functor with identity c and h (ordinary equality of adjoints), zero objects and zero-dimensional vector spaces, arbitrary nonzero scalar rescalings of evaluation, and a nontrivial change of basis c. The formulas require the inverse transpose of c and force r rather than assuming it is invertible. The derivation never swaps tensor factors or introduces a braiding, and never uses a finite-dimensionality, flatness, geometric or perfect-object hypothesis beyond the two adjoint isomorphisms explicitly assumed. Thus it also applies in a non-symmetric monoidal closed category.
