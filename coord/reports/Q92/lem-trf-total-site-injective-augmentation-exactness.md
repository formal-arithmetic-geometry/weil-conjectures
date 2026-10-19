Files written:

- `dag/nodes/sec-trace-formula/lem-trf-total-site-injective-augmentation-exactness.json` — statement, split proof, no new nodes, no Mathlib leaf.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none.

WANTED: none.

No statement or source error was found. The item is the injective case of Stacks Tag 0D79, and its hypotheses allow the coherent pseudo-functor identifications stated in the item. No new node was created: the existing total-site component-restriction node already states the exact left adjoints, component formula, exactness, and conservativity needed for the free simplicial resolution.

Nothing remains unfinished.

## Review by Q92

I read the item and the full proof of Stacks `spaces-simplicial.tex`, Tag 0D79 (lines 1770–1800), together with the preceding exact augmented simplicial resolution used there (Tag 0D78, lines 1711–1768). I also read the complete statement of `lem-trf-total-site-component-restriction`, `def-trf-geometric-morphism`, `def-weil-pbc-simplicial-object`, and `def-sp-injective-resolutions`. Step 1 uses exactly the component lemma's formula for `g_{p!}`, exactness of each restriction, and conservativity; the displayed extra-degeneracy is the standard contraction of the simplex chain complex, and I checked it on the identity simplex and on a constant point site. Step 2 uses only the two adjunctions stated by the geometric-morphism and component-restriction nodes; tracing the adjunction maps gives the item's coface maps and counit augmentation. Step 3 uses precisely the injective extension property stated in `def-sp-injective-resolutions`, including the degree-zero factorization through the augmentation epimorphism. Step 4 is the functorial Yoneda exactness test in the abelian sheaf category, with naturality obtained by postcomposition. I checked the empty and point-site cases and the constant simplicial diagram: the complex contracts to the degree-zero term and the augmentation is the expected identity. The existing Mathlib search records were read and retained; they report no matching Mathlib theorem. No duplicate node or hidden additional hypothesis was introduced.
