# Stage-1 report: lem-trf-comonad-mixed-degeneracy-identities

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-comonad-mixed-degeneracy-identities.json`: statement, split; six proof steps. Mathlib verdict: no exact match, since the simplicial relations found require a supplied simplicial object, whereas this item proves relations for raw whiskered transformations.
- `citations.json`: exact statement quotations for each dependency of each proof step.
- `report.md`: this report. `searches.jsonl` was produced by msearch.py; five new queries were actually run and their returned records appended to the item's existing searches.

New nodes: 0. New Mathlib leaves: 0. Reused Mathlib leaf: `lem-amb-natural-transformation-whisker-exchange`.

## Attachments

None. Searched project WeilConjectures by exact blueprint tag, comonad/Comonad, mixed/degeneracy and related notions. The Godement module-cup files concern a particular monad on scheme modules (dual variance and special category), not arbitrary endofunctors with the hypotheses of this item. They do not supply all its clauses.

## WANTED

None. The needed Stacks sources are present.

## Errors and changes

The item was statement-only and had no proof. Its statement is retained exactly: every index range is meaningful, and no existing simplicial object is assumed. The Mathlib simplicial identities are therefore not evidence of completion. The source's phrase "same kind of calculus" in the disjoint cases is replaced by explicit intermediate powers and substitutions in the existing exchange lemma. No statement dispute, route change or new definition was needed.

The current blueprint under literature/blueprint/latest/ was read at sec-trace-formula/sk-i-curve-zero, including the locality statement, its proof file and the unit. This auxiliary comonad item lies on the inherited standard-resolution branch; it is not itself a current blueprint statement. Searches of the whole DAG and blueprint for comonad, degeneracy, horizontal composition, whiskered and interchange found no blueprint node with this exact statement. The existing ancestor and via chain remain intact; same_as is []. This is not the unit's key node, so no realized fields are changed.

## Unfinished work

None in this stage-1 split. No Lean was written, compiled or built. All writes were confined to the assigned sandbox; required server checks and delivery are run through the provided scripts.

## Not duplicates

No new nodes were created. The existing exchange node was reused rather than duplicated. The neighboring face-identities node states two-face relations without a comultiplication, not the mixed and degeneracy clauses here; it is not used to supply a missing interchange claim.

## Review by Q126

I read Stacks simplicial.tex Example 0G5M (example-godement) and Lemma 0G5N (lemma-godement), particularly the proof of (1)(b)--(e), and categories.tex Lemma 003F (lemma-properties-2-cat-cats), which supplies the interchange calculus used there. There are no new nodes whose sources need independent review. I also read the full statements of both cited DAG nodes, not their proofs, and the Mathlib exchange declaration in CategoryTheory/Whiskering.lean:203-207. The existing exchange statement says exactly that (K eta)(theta F)=(theta G)(H eta), with no additional hypotheses; the citation file copies that formula verbatim.

Step 1 uses only the recursion actually stated in def-trf-endofunctor-powers. I supplied the zero case and successor calculation for addition of powers. The component formulas and their naturality follow by applying T^i to the naturality equation of e or c at T^{n-i}(f); the two target powers are respectively n and n+2. This establishes naturality without assuming a simplicial functor.

Step 2 uses the exchange statement with eta=1_k star c and theta=e, after fixing k=j-i-1 and r=n-j-1. Its functors are F=T^{k+1}, G=T^{k+2}, H=T and K=id. Substitution gives precisely the two written composites. Step 3 uses eta=1_k star e and theta=c, with k=i-j-2, r=n-i, F=T^{k+1}, G=T^k, H=T and K=T^2. Again the exchange formula gives exactly the two displayed composites. I checked each remaining outer T-power and each total source/target, so these are applications of the cited statement rather than references to its proof.

Step 4 uses the two counit identities that are hypotheses of this item, evaluated at T^r x and mapped by T^j; functoriality gives each displayed whiskered composite and turns the identity into 1_n. There is no theorem about an abstract comonad being silently invoked. Step 5 uses the same exchange node with eta=1_k star c and theta=c. Here F=T^{k+1}, G=T^{k+2}, H=T, K=T^2; the two non-overlapping insertions both have normal form c star 1_k star c. Step 6 uses exactly the stated coassociativity hypothesis, evaluated at T^{n-1-i}x and mapped by T^i. Thus the overlapping degeneracies are proved separately and are not incorrectly treated as disjoint insertions.

I checked n=1, j=0 for both counit composites: they reduce to (e star 1)c and (1 star e)c. For the degeneracy relation n=1,i=j=0 is exactly coassociativity. The first disjoint mixed case starts at n=2,i=0,j=1 and has k=r=0; the other starts at n=2,j=0,i=2 and likewise has zero middle and final powers. All other zero exponents at the endpoints use 1_0 on the identity functor. The distinct-degeneracy case i=0,j=1,n=2 is the exchange square for c and c with k=r=0. Also T=id and e=c=id makes every formula the identity, and the empty category creates no nonemptiness requirement.

Against delivery-errors B--E: there are no new nodes to be non-self-contained, duplicated, elementary or merely renamed clauses. The proof uses the existing exchange Mathlib leaf for the only nontrivial categorical calculus; the remaining substitutions, functoriality and given axioms are explicitly written elementary steps. Each dependency is quoted verbatim in citations.json; no proof of another node is borrowed, and no tags substitute for dependency nodes. There is no upward citation to the parent simplicial-construction node, hence no circular appeal to the conclusion. Each step is under 2000 characters and contains no hidden standard comparison or standalone auxiliary lemma. The unit route and inherited statement are unchanged. No SGA source is used.

I inspected the new actual Mathlib search results and their candidate declarations: Comonad in Monad/Basic.lean:60-83 gives the original three axioms and naturality, and SimplicialObject/Basic.lean:148-199 gives relations only for an already constructed simplicial object. The two LeanFinder phrasings and LeanSearch returned these kinds of relations or extra-degeneracy tools, not this item. The existing searches were retained and the actual new search records appended; no unavailable service was represented as an absence result.
