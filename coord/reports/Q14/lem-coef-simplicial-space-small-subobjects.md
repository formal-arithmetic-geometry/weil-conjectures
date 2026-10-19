# Stage-1 report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-space-small-subobjects.json`: six-step split; original statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim excerpt for every node cited in every proof step.

## Attachments

None. Searches for the item tag and for bounded bisimplicial/presheaf/cardinal-presentability assertions in the read-only project Lean source found no project declaration stating the item. Upstream sorry declarations were not used as finished proofs.

## WANTED

None for this self-contained argument: the sole non-elementary input is the existing Mathlib leaf `lem-coef-accessible-set-functor-limits`. The inherited Rezk/Bousfield–Smith context is not asserted to be an archived source proof of this lemma.

## What was wrong and what changed

The imported statement is true, but its proof was empty. Its source names an agent-formulated auxiliary assertion under paragraph 2 of the integral-adjoint blueprint proof; that paragraph itself discusses derived coefficient adjunction, not cardinal bounds for simplicial spaces. I read the blueprint statement and proof and retained the historical ancestry while explicitly labeling this auxiliary argument agent-written. The chapter and unit are unchanged. The item is not a unit key node and no unit realization fields are edited.

The final proof uses the bounded category-of-elements formula for Hom directly and the existing small-limit commutation Mathlib leaf, instead of introducing nodes for bounded-presheaf or arrow presentability. The never-committed draft nodes were removed. This avoids restating the presentability clause in a descendant. The statement was neither weakened nor repaired; there is no statement dispute.

## Review by Q14

I read `coord/delivery-errors.md` B–E in full and checked the final files against its substantive requirements. I read the item's source, `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, and its companion statement, as well as the chapter and unit records. There are no new nodes requiring separate source attribution, duplicate checks, or Mathlib verdicts. DAG/blueprint searches found no existing node stating the whole item, and source searches found no Lean attachment. The original item Mathlib-search history is preserved; additional searches actually run through msearch.py remain in searches.jsonl. Some early grep queries incorrectly supplied a subdirectory beginning with Mathlib/ and returned no hits; these outputs were not treated as evidence of absence. A corrected grep with CategoryTheory/Presentable and a direct reading of the cited Mathlib declaration confirm the actual input.

Step 1 uses precisely the definition of simplicial sets from `def-weil-pbc-simplicial-set` and the universal property from `def-weil-pbc-category-colimit`. Expanding the functor laws identifies commuting squares with diagrams on [1] times the two opposite simplex categories, including mixed naturality. Componentwise colimits and evaluation preservation are justified by constructing the operators and testing component naturality on every coprojection.

Step 2 uses no external theorem: it defines the elements category explicitly. An arrow is fixed by a source element and an arrow of D; regularity bounds this disjoint union of fewer than gamma small sets. The three possible arrows in [1] multiply the countable indexing-arrow set only by a finite factor. Empty endpoints are allowed, and the entirely empty diagram gives the empty elements category.

Step 3 is the only non-elementary step. I opened and read the full statement of `lem-coef-accessible-set-functor-limits`, and read `Mathlib/CategoryTheory/Presentable/Limits.lean:158–168`. It states preservation of cardinal-filtered colimits by a limit of set-valued functors indexed by fewer than gamma morphisms, without requiring accessibility of the domain category. These are exactly the hypotheses supplied here by steps 1 and 2. The Hom-limit identification is written as mutually inverse formulas: u maps to its values u_d(x), and a compatible family gives u_d by x mapping to t_(d,x). Its compatibility equation is precisely naturality, and applying G to G' acts componentwise, so this identification is natural. Thus this is a routine limit calculation, not an unproved comparison theorem. The empty indexing category is expressly allowed by the cited leaf. Citation excerpts were extracted directly from each cited statement, including its TeX punctuation.

Step 4 proves smallness using a powerset of the total simplex set and proves cardinal filteredness by unions, including the empty subspace. Identity morphisms bound the number of objects in any test category; a common upper bound therefore gives the required cocone, rather than merely pairwise directedness.

Step 5 writes the generated subspace concretely using pairs of order-preserving maps. Closure uses composition, and the identity contains the original simplex; its total cardinality is bounded by the morphisms of the product simplex category. Both endpoint unions are proved, with X identified with its degreewise image in Y as appropriate for a monomorphism. No assumption of finiteness, nonemptiness, or fibrancy is introduced.

Step 6 uses only the colimit universal property. Given any cocone of squares, it constructs both component maps on individual simplices. The bounded union of two choices proves independence, closure under operators proves naturality, the original square equations prove the resulting square, and exhaustion proves uniqueness. Thus it verifies the specified canonical arrow cocone, not an unspecified isomorphic colimit. For X or Y empty, the same formulas give the unique empty-source maps.

No proof step exceeds 2000 characters (the longest is approximately 1000); I nevertheless checked the category-of-elements Hom calculation and the union calculation for hidden lemmas. All non-elementary input is the cited existing Mathlib leaf. No off-unit route change, SGA reference, new definition node, cycle through the parent, or new hollow assertion is introduced. No Lean was written and no compiler, Lake, or build command was run.

## What could not be finished

Nothing mathematical remains in this one-level split. A second reader must review and deliver; this worker runs only the required no-push dry run.

## Second reading by Q14

- Item statement: checked against the agent-formulated auxiliary argument and the surrounding `prop-coef-integral-exceptional-adjoint` blueprint proof; all hypotheses and conclusions are retained, with no literal Stacks tag present in the source; verdict: PASS.
- Step 1: checked the arrow-category identification against the definition of simplicial sets and the colimit universal property; pointwise colimits and the mixed naturality equations are correct; verdict: PASS, elementary.
- Step 2: checked the category-of-elements construction and the bounds on objects and arrows for regular uncountable `\gamma`, including the empty diagram; verdict: PASS, elementary.
- Step 3: checked the natural Hom/limit bijection and its naturality against `lem-coef-accessible-set-functor-limits` and the Mathlib source at `Presentable/Limits.lean:158–168`; the bound `|Mor E|<\gamma` supplies the leaf hypothesis; verdict: PASS.
- Step 4: checked the powerset smallness, unions, regularity, and cocone argument for `I_\gamma(Y)`; the empty subspace handles the empty diagram; verdict: PASS, elementary.
- Step 5: checked the generated subspace of a simplex in degrees `n=0,1`, closure under both simplicial directions, degreewise monomorphism interpretation, and exhaustion of `X` and `Y`; verdict: PASS, elementary.
- Step 6: checked the explicit arrow-colimit universal property, independence via `B\cup B'`, naturality, square compatibility, and uniqueness; verdict: PASS, elementary.
- New nodes: none. The inherited dependencies were read; no duplicate, restatement, or missing Mathlib leaf was found.

I tested the empty bisimplicial object and empty subspace, the zero-to-nonempty arrow, and one-simplex examples in degrees `(0,0)` and `(1,0)`; all formulas specialize correctly. A field or empty scheme is inapplicable because the statement has no ring or scheme parameters. I also rechecked the item and dependency metadata, the citation excerpts, the blueprint ancestry, and the recorded Mathlib searches. No files required repair.
