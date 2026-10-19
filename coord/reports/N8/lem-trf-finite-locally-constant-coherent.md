# Stage 1 report: lem-trf-finite-locally-constant-coherent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-locally-constant-coherent.json`: one statement node, split; no new nodes.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its title, and finite-locally-constant/coherent terminology; no sorry-free project declaration states this item.

## WANTED:

None. The split follows the locally available Stacks `sites-modules.tex`; the Orgogozo §8.1 source is cited by the imported blueprint but is not needed as a separate file.

## Not duplicates

No new nodes were created. The existing nodes `lem-trf-finitary-site-coherent-generators`, `lem-trf-coherent-object-approximation`, `lem-trf-coherent-epimorphic-quotient`, and `lem-trf-set-sheaf-finite-extensivity` are generic inputs and do not state finite locally constant closure; the existing `lem-trf-oriented-constructible-coherent` concerns finite module sheaves on a Noetherian vanishing topos and is a different statement.

## Review by N8

I read the item, its unit `sk-i-curve-zero`, chapter `sec-trace-formula`, and the cited definition nodes. I also read the complete statements of the finite-cover coherent-generator criterion, coherent-object finite-limit/coproduct closure, the coherent epimorphic-quotient criterion, finite extensivity of set sheaves, and the constant-sheaf definition. Step 1 uses the finite-cover criterion to obtain coherent representables and the existing finite-coproduct closure; the hypotheses are exactly the small finite-limit site and finite covering families in the item. Step 2 checks the actual finite presentation: the local finite constant models give an epimorphism from a finite coproduct of representables, and after refining by pairwise fibre products and the finite trivializing covers, the kernel pair is covered by finitely many finite coproducts of representables, hence is quasi-compact. The cited quotient criterion then applies with the coherent source and quasi-compact kernel pair. Steps 3–5 use one common finite refinement. Finite limits and coproducts are computed on finite sets; a morphism is decomposed by the finitely many coproduct summands, so its image is locally a finite constant image set; an internal equivalence relation is similarly a finite relation and its coequalizer is locally the finite quotient set. The finite extensivity statement supplies the disjoint pullback decompositions used in these refinements, while the constant-sheaf definition supplies the local models. I checked empty finite sets, empty coproducts, the terminal sheaf, identity and constant maps, and the equality relation; all clauses remain valid. No hypotheses were silently added, no SGA 4 source was used, and no existing node was duplicated.
