Files written:

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-constructible-noetherian-finite-selection.json` (statement, split; no new nodes).
- `citations.json` (four cited-node quotes).

Attachments: none.

WANTED: none.

The item had no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and is not a Mathlib theorem. I found no duplicate blueprint node or DAG node stating the finite-selection lemma. The imported proof was a single paragraph and its `uses` omitted the exact-stalk and stalk-conservativity lemmas used in its final sentence. I split it into four steps, made the finite choice and stalk projection explicit, and added those two dependencies. The item statement and hypotheses were left unchanged.

## Review by C1

I read the item source in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-constructible-noetherian-finite-selection.md`, and read the statements of `lem-weil-pbc-irreducible-lisse-strata`, `lem-weil-pbc-lisse-generic-kernel`, `prop-weil-pbc-geometric-stalks-exact`, and `lemma-weil-pbc-geometric-stalk-conservative`. Step 1 takes exactly the finite partition and finite-stalk conclusion stated by the strata node. Step 2 is the finite-set choice from the hypothesis and the finiteness of the selected generic stalk, so it is elementary. Step 3 uses precisely the generic-kernel node's implication from injectivity at the geometric generic point to a monomorphism, then uses only finite-union and finite-sum projection identities. Step 4 uses exactness of the stalk functor to identify the kernel stalks and the conservativity node to conclude that the kernel is zero; both cited statements explicitly provide those facts. I checked that no target-sheaf finiteness is used. I also tested the construction in the empty-index and singleton cases: the hypotheses force the relevant stalk to be zero in the empty case, while a singleton family gives the stated “in particular” clause. The Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; no matching declaration was found (LeanSearch was unavailable), and their exact results are recorded in the node.

## Second reading by C1

- Item statement: checked against Stacks etale-cohomology.tex Lemma 09Z6 (lemma-constructible-maps-into-constant), including its parenthetical finite partition alternative; verdict: mathematically consistent and stronger in allowing an arbitrary stalk-detecting family.
- Step 1: checked against `lem-weil-pbc-irreducible-lisse-strata`; verdict: cited statement supplies exactly the finite irreducible locally closed partition and finite locally constant stalks.
- Step 2: checked from the finite stalks and the hypothesis; verdict: elementary finite choice, including empty and singleton cases.
- Step 3: checked against `lem-weil-pbc-lisse-generic-kernel`; verdict: generic injectivity gives a monomorphism on each stratum, and projection from the larger finite sum is elementary.
- Step 4: checked against `prop-weil-pbc-geometric-stalks-exact` and `lemma-weil-pbc-geometric-stalk-conservative`; verdict: exactness identifies kernel stalks and conservativity gives the global monomorphism.
- Existing nodes: no new nodes are needed; duplicate and Mathlib searches found no replacement theorem for the item.
- Changed the item's blueprint metadata to its own ancestor and recorded the exact proof place.
- Changed the item source and proof origins to Stacks Lemma 09Z6 and its partition alternative.
- Corrected the kernel conclusion from the ill-directed map `0 → K` to the correct map `K → 0`.
