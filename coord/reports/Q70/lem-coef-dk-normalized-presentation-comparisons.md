# Stage-1 report: lem-coef-dk-normalized-presentation-comparisons

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dk-normalized-presentation-comparisons.json`: statement split into four complete proof steps; no new node and no Mathlib leaf.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, its title and the normalized comparison terminology; no sorry-free project declaration states this item exactly.

## WANTED

WANTED: an archival local copy of Lurie, *Higher Topos Theory*, §2.2.3.11 (the source URL is recorded in the node). The normalized homotopy-fibre lemma is agent-formulated from the cited mapping-space background; no Stacks tag states it.

## Not duplicates

No new node was created. The existing `lem-coef-space-contractible-fiber-equivalence` is a generic criterion for weak equivalences of Kan complexes and does not state enriched composition compatibility or the inverse-data clause, so it is cited rather than duplicated.

## What was checked and corrected

The imported item had an empty proof. I retained its statement and dependencies, filled its blueprint proof place, and added four steps. The first step checks that local Kan hypotheses make both mapping complexes Kan, identifies the displayed degreewise pullback with the definition’s path-space homotopy fibre, and applies the existing contractible-fibre criterion. The second step writes the enriched composition of two comparison paths degreewise and explains why all higher parameters remain in the normalized fibre. The third step uses an inverse vertex and its two target homotopies, lifts the inverse comparison through the contractible normalized fibre, and compares the resulting composite with the identity point in the identity fibre to obtain both inverse homotopies. The fourth step writes the precomposition map by a fixed enriched homotopy equivalence and its explicit simplicial homotopy inverse; it invokes `lem-cbc-simplicial-homotopy-equivalence-weak` as a declared generic tool, then applies the contractible-fibre criterion to obtain the inverse-data fibre and its second homotopy.

I read the full statements of `def-cbc-enhanced-diagrams-cones`, `def-coef-coherent-nerve-infrastructure`, `lem-coef-space-contractible-fiber-equivalence`, and `lem-cbc-simplicial-homotopy-equivalence-weak`. Each cited quote in `citations.json` is copied verbatim from those statements. The hypotheses are used as follows: local Kan gives Kan mapping complexes; the enriched functor gives the mapping maps and preserves composition; the existing fibre criterion applies to each weak equivalence; and the off-unit tool applies only to the explicit simplicial homotopy inverse in the final step. The item’s four Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`; all returned only unrelated model-category or Kan-complex declarations.

Small cases checked: for an identity mapping-space map, the normalized fibre is the path space ending at the chosen vertex and is contractible; if the target mapping complex has no chosen vertex, the item has no instance; and for a simplicial groupoid the inverse-data fibre keeps the specified first inverse homotopy even when the unnormalized equivalence space has nontrivial automorphisms. No statement error, unsupported hypothesis, forbidden SGA source, or proof step over 2000 characters was found.

## Review by Q70

I reread the item beside both definition nodes and the two theorem nodes. Step 1 uses exactly the path-pullback model from `def-cbc-enhanced-diagrams-cones` and the local-Kan clause from `def-coef-coherent-nerve-infrastructure`; the weak-equivalence hypothesis is precisely the input required by `lem-coef-space-contractible-fiber-equivalence`. Step 2 uses only the degreewise enriched composition and the degreewise simplicial pullback conventions, so its elementary classification is justified. In Step 3 I verified the source and target of each composite (`c:y→x`, `a:x→y`) and checked that the two prescribed target inverse homotopies end at the correct identity vertices; the identity point and the composite point lie in the same normalized identity fibre, whose contractibility supplies the source homotopy. In Step 4 I checked the variance of `r(h)=h∘f` and `s(k)=k∘g`, the associativity composites, and the endpoint homotopies required by the off-unit tool. Every step’s cited statements say the fact taken from them, and every quote is verbatim in `citations.json`. The proof preserves normalized comparison paths and higher simplices throughout and does not assert contractibility of the unnormalized equivalence space.

## What remains

No unfinished split work remains. The item is ready for the required server dry run.
